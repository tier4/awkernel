# Memory Allocator

Awkernel uses [rlsf](https://github.com/yvt/rlsf), which implements Two-Level Segregated Fit (TLSF) memory allocator.
The `Tallock` structure represents an allocator in Awkernel,
which contains a primary allocator and a backup allocator.
Async/await tasks use only the primary allocator,
but kernel tasks, such as interrupt handlers,
use both the primary and the backup allocators for safety.
Because of the backup allocator,
kernel tasks can safely handle memory exhaustion in the primary allocator.

The `Tallock` structure is defined in [awkernel_lib/src/heap.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/heap.rs) as follows.

```rust
struct Allocator(Mutex<TLSFAlloc>);
struct BackUpAllocator(Mutex<TLSFAlloc>);

pub struct Talloc {
    primary: Allocator,
    backup: BackUpAllocator,

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

There are 2 functions to initialize memory regions of the primary and backup allocators.

| function | description |
|----------|-------------|
| `fn init_primary(primary_start: usize, primary_size: usize)` | Initialize the memory region of the primary allocator. |
| `fn init_backup(backup_start: usize, backup_size: usize)` | Initialize the memory region of the backup allocator. |

# Initialization

## x86_64

For x86_64, the primary and backup allocators are initialized
in `init_primary_heap` and `init_backup_heap` functions defined in
[kernel/src/arch/x86_64/kernel_main.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/x86_64/kernel_main.rs) as follows.
These functions initialize virtual memory regions for the primary and backup heaps
before initializing the primary and backup allocators.

```rust
fn init_primary_heap(
    page_table: &mut OffsetPageTable<'static>,
    page_allocators: &mut BTreeMap<u32, VecPageAllocator>,
) {
    let primary_start = HEAP_START + BACKUP_HEAP_SIZE;

    let num_pages = map_primary_heap(page_table, page_allocators, primary_start);

    let heap_size = num_pages * PAGESIZE;
    unsafe { awkernel_lib::heap::init_primary(primary_start, heap_size) };

    // omitted
}
```

```rust
fn init_backup_heap(
    boot_info: &mut BootInfo,
    page_table: &mut OffsetPageTable<'static>,
) -> (usize, MemoryRegion, Option<PhysFrame>) {
    // omitted: Initialize virtual memory regions for the backup heap.

    // Initialize.
    // Enable heap allocator.
    unsafe {
        awkernel_lib::heap::init_backup(HEAP_START, BACKUP_HEAP_SIZE);
        awkernel_lib::heap::TALLOC.use_primary_then_backup();
    }

    (backup_pages, backup_heap_region, next_page)
}
```

## AArch64

For x86_64, the primary and backup allocators are initialized
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

    heap::init_primary(primary_start, primary_size);
    heap::init_backup(backup_start, backup_size);

    // omitted
}
```
