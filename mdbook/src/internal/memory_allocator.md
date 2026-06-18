# Memory Allocator

Awkernel uses [rlsf](https://github.com/yvt/rlsf), which implements Two-Level Segregated Fit (TLSF) memory allocator.
The `Tallock` structure represents an allocator in Awkernel,
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

## RISC-V 32-bit (RV32)

For RISC-V 32-bit, the primary and backup allocators are initialized
in `primary_hart` function defined in
[kernel/src/arch/rv32/kernel_main.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/rv32/kernel_main.rs) as follows.

**Unlike x86_64 and AArch64, RISC-V initializes heap allocators BEFORE setting up virtual memory.**
This is because the page table allocation itself requires heap memory.
The initialization order is:
1. Initialize heap allocators (lines 89-92)
2. Initialize page allocator (line 123)
3. Initialize and activate virtual memory (lines 126-129)

```rust
unsafe fn primary_hart(hartid: usize) {
    // omitted

    // setup the VM
    let backup_start = HEAP_START;
    let backup_size = BACKUP_HEAP_SIZE;
    let primary_start = HEAP_START + BACKUP_HEAP_SIZE;
    let primary_size = HEAP_SIZE;

    // enable heap allocator
    heap::init_primary(primary_start, primary_size);
    heap::init_backup(backup_start, backup_size);
    heap::TALLOC.use_primary_then_backup(); // use backup allocator

    // omitted

    // Initialize memory management (page allocator)
    awkernel_lib::arch::rv32::init_page_allocator();

    // Initialize virtual memory system
    awkernel_lib::arch::rv32::init_kernel_space();

    // Activate virtual memory (enable MMU and page tables)
    awkernel_lib::arch::rv32::activate_kernel_space();

    // omitted
}
```

## RISC-V 64-bit (RV64)

For RISC-V 64-bit, the primary and backup allocators are initialized
in `init_heap_allocation` function defined in
[kernel/src/arch/rv64/kernel_main.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/rv64/kernel_main.rs) as follows.

**Like RV32, RV64 also initializes heap allocators BEFORE setting up virtual memory,**
as stated in the comment "Setup heap allocation FIRST - page tables need this!"
The initialization order in `primary_hart` function is:
1. Initialize UART for early debugging (line 241)
2. Setup heap allocation (line 244, calling `init_heap_allocation()`)
3. Initialize memory management including page allocator and virtual memory (line 247, calling `init_memory_management()`)
4. Initialize architecture-specific features, console, timer, and interrupts

RV64 has additional unique features:
- Uses the `ekernel` symbol to determine heap start address dynamically
- Implements dynamic heap sizing with `get_heap_size()` based on available memory
- Has fallback logic for minimal heap configuration (64MB) when memory is limited

```rust
unsafe fn init_heap_allocation() {
    // omitted

    extern "C" {
        fn ekernel();
    }

    let heap_start = (ekernel as usize + 0xfff) & !0xfff; // Align to 4K
    let backup_size = BACKUP_HEAP_SIZE;
    let total_heap_size = awkernel_lib::arch::rv64::get_heap_size();

    if total_heap_size <= backup_size {
        // Use minimal heap if not enough memory
        let primary_size = 64 * 1024 * 1024; // 64MB minimum
        heap::init_primary(heap_start + backup_size, primary_size);
        heap::init_backup(heap_start, backup_size);
    } else {
        // Use dynamic calculation
        let primary_size = total_heap_size - backup_size;
        heap::init_primary(heap_start + backup_size, primary_size);
        heap::init_backup(heap_start, backup_size);
    }

    heap::TALLOC.use_primary_then_backup();

    // omitted
}
```
