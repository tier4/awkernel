# Memory Allocator

The heap backend in Awkernel is selected at compile time by feature flags.

- `heap-wf-alloc` selects the wait-free [wf_alloc](https://github.com/ytakano/wf_alloc) backend, supported on `x86_64` and `aarch64`.
- Otherwise, the [rlsf](https://github.com/yvt/rlsf) Two-Level Segregated Fit (TLSF) backend is used.

The two features are mutually exclusive; enabling both fails the build with a `compile_error!`.
The `kernel` crate enables `heap-wf-alloc` on x86 by default, while TLSF remains for other targets.

Regardless of the backend, the `Talloc` structure represents the allocator in Awkernel,
which contains a primary allocator and a backup allocator.
Async/await tasks use only the primary allocator,
but kernel tasks, such as interrupt handlers,
use both the primary and the backup allocators for safety.

The following code shows how to use the primary and backup allocators in the task scheduler defined in
[awkernel_async_lib/src/task.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/task.rs).

```rust
pub fn run_main() {
    loop {
        if let Some(task) = get_next_task() {
            // Use the primary memory allocator.
            #[cfg(not(feature = "std"))]
            unsafe {
                awkernel_lib::heap::TALLOC.use_primary()
            };

            let result = catch_unwind(|| {
                guard.poll_unpin(&mut ctx)
            });

            // Use the primary and backup memory allocator.
            unsafe {
                awkernel_lib::heap::TALLOC.use_primary_then_backup()
            };
        }
    }
}
```

In `run_main` function, a executable task is taken from the task queue by `get_next_task` function.
Before executing the task, `awkernel_lib::heap::TALLOC.use_primary()` is called to use only the primary memory allocator.
The task is executed by calling `poll_unpin` method in the `catch_unwind` block to catch a panic.
If the task exhausts the primary memory region, it will panic and `run_main` function will catch the panic.
After catching the panic, `awkernel_lib::heap::TALLOC.use_primary_then_backup()` is called to use both the primary and backup memory allocators,
and safely deallocate the task.

Each backend implements the `HeapBackend` trait, defined in
[awkernel_lib/src/heap.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/heap.rs) as follows.

```rust
trait HeapBackend {
    /// Initialize the backend over the `[heap_start, heap_start + heap_size)` region.
    /// `active_threads` is the number of CPUs that can use the heap concurrently.
    /// Returns `Err(reason)` if the backend could not be initialized.
    unsafe fn init(
        &self,
        heap_start: usize,
        heap_size: usize,
        active_threads: usize,
    ) -> Result<(), &'static str>;

    unsafe fn alloc(&self, layout: Layout) -> *mut u8;

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout);
}
```

The backend is chosen by a compile-time type alias.

```rust
// `heap-wf-alloc` on x86_64 / aarch64:
type Allocator = wf_alloc_backend::WfAllocBackend;

// otherwise:
type Allocator = tlsf_backend::TlsfBackend;
```

The `Talloc` structure holds a primary and a backup allocator of the selected backend.

```rust
pub struct Talloc {
    primary: Allocator,
    backup: Allocator,

    /// bitmap for each CPU to decide which allocator to use
    flags: [AtomicU32; NUM_MAX_CPU / 32],

    primary_start: AtomicUsize,
    primary_size: AtomicUsize,
    backup_start: AtomicUsize,
    backup_size: AtomicUsize,
}
```

The `Talloc` structure is defined as a global allocator as follows.

```rust
#[global_allocator]
pub static TALLOC: Talloc = Talloc::new();
```

The following functions initialize the memory regions of the primary and backup allocators.

| function | description |
|----------|-------------|
| `fn init_primary(primary_start: usize, primary_size: usize)` | Initialize the primary allocator, using `cpu::num_cpu()` as the CPU count. |
| `fn init_backup(backup_start: usize, backup_size: usize)` | Initialize the backup allocator, using `cpu::num_cpu()` as the CPU count. |
| `fn init_primary_with_num_cpu(primary_start: usize, primary_size: usize, num_cpu: usize)` | Initialize the primary allocator with an explicit CPU count. |
| `fn init_backup_with_num_cpu(backup_start: usize, backup_size: usize, num_cpu: usize)` | Initialize the backup allocator with an explicit CPU count. |

The `wf_alloc` backend maps each CPU id directly to a per-CPU token and must know the
number of CPUs that can use the heap concurrently (`active_threads`) at initialization time,
because it sizes its metadata region from that count. If the count is `0`, allocator
initialization fails and the kernel halts during heap setup. The TLSF backend ignores the count.
The bare `init_primary` / `init_backup` read this count from `cpu::num_cpu()` internally, so
they only behave correctly after the active CPU count has been established. On x86_64 the
heap is initialized before that count is set (so `cpu::num_cpu()` would return `0`); the boot
code therefore uses the `init_primary_with_num_cpu` / `init_backup_with_num_cpu` variants and
passes the CPU count it detected from ACPI explicitly.

# Initialization

## x86_64

For x86_64, the primary and backup allocators are initialized
in `init_primary_heap` and `init_backup_heap` functions defined in
[kernel/src/arch/x86_64/kernel_main.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/x86_64/kernel_main.rs) as follows.
These functions initialize virtual memory regions for the primary and backup heaps
before initializing the primary and backup allocators.

The `num_cpu` argument is the CPU count detected from ACPI during boot, passed through to
the `*_with_num_cpu` initializers.

```rust
fn init_primary_heap(
    page_table: &mut OffsetPageTable<'static>,
    page_allocators: &mut BTreeMap<u32, VecPageAllocator>,
    num_cpu: usize,
) {
    let primary_start = HEAP_START + BACKUP_HEAP_SIZE;

    let num_pages = map_primary_heap(page_table, page_allocators, primary_start);

    let heap_size = num_pages * PAGESIZE;
    unsafe { awkernel_lib::heap::init_primary_with_num_cpu(primary_start, heap_size, num_cpu) };

    // omitted
}
```

```rust
fn init_backup_heap(
    boot_info: &mut BootInfo,
    page_table: &mut OffsetPageTable<'static>,
    num_cpu: usize,
) -> (usize, MemoryRegion, Option<PhysFrame>) {
    // omitted: Initialize virtual memory regions for the backup heap.

    // Initialize.
    // Enable heap allocator.
    unsafe {
        awkernel_lib::heap::init_backup_with_num_cpu(HEAP_START, BACKUP_HEAP_SIZE, num_cpu);
        awkernel_lib::heap::TALLOC.use_primary_then_backup();
    }

    (backup_pages, backup_heap_region, next_page)
}
```

## AArch64

For AArch64, the primary and backup allocators are initialized
in `primary_cpu` function defined in
[kernel/src/arch/aarch64/kernel_main.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/aarch64/kernel_main.rs) as follows.

```rust
unsafe fn primary_cpu(device_tree_base: usize) {
    // omitted

    // 5. Enable heap allocator.
    let backup_start = HEAP_START;
    let backup_size = BACKUP_HEAP_SIZE;
    let primary_start = HEAP_START + BACKUP_HEAP_SIZE;
    let primary_size = vm.get_heap_size().unwrap() - BACKUP_HEAP_SIZE;
    let num_cpu = initializer.get_num_cpus();

    heap::init_primary_with_num_cpu(primary_start, primary_size, num_cpu);
    heap::init_backup_with_num_cpu(backup_start, backup_size, num_cpu);

    // omitted
}
```
