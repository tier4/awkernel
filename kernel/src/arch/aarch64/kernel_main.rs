//! # Boot process
//!
//! 1. The entrypoint, `_start` in `kernel/asm/aarch64/boot.S`, is called.
//! 2. [`kernel_main`] is called.
//! 3. For the primary CPU, [`primary_cpu`] is called and some initializations are performed.
//! 4. For non-primary CPUs, [`non_primary_cpu`] is called.

use super::cpu;
use crate::{
    arch::aarch64::bsp::SoC,
    config::{BACKUP_HEAP_SIZE, HEAP_SIZE, HEAP_START},
    kernel_info::KernelInfo,
};
use awkernel_lib::{
    console::{unsafe_print_hex_u32, unsafe_puts},
    delay::wait_forever,
    device_tree::device_tree::DeviceTree,
    heap, local_heap,
};
use core::{
    ptr::{read_volatile, write_volatile},
    sync::atomic::{AtomicBool, Ordering},
};

static mut PRIMARY_READY: bool = false;
static PRIMARY_INITIALIZED: AtomicBool = AtomicBool::new(false);

static mut TTBR0_EL1: usize = 0;

/// The entry point from `boot.S`.
#[no_mangle]
pub unsafe extern "C" fn kernel_main(device_tree_base: usize) -> ! {
    awkernel_aarch64::init_cpacr_el1(); // Enable floating point numbers.

    awkernel_lib::delay::wait_millisec(10);

    if cpu::core_pos() == 0 {
        primary_cpu(device_tree_base);
    } else {
        while !read_volatile(&PRIMARY_READY) {}
        non_primary_cpu();
    }

    wait_forever();
}

/// 1. Initialize the device (UART, etc.).
/// 2. Initialize the virtual memory.
/// 3. Start non-primary CPUs.
/// 4. Enable MMU.
/// 5. Enable heap allocator.
/// 6. Board specific initialization (Interrupt controller, etc).
unsafe fn primary_cpu(device_tree_base: usize) {
    let device_tree = load_device_tree(device_tree_base);
    let mut initializer = super::bsp::SoCInitializer::new(device_tree, device_tree_base);

    // 1. Initialize device (UART, etc.).
    if initializer.init_device().is_err() {
        wait_forever();
    }

    match awkernel_aarch64::get_current_el() {
        0 => unsafe_puts("EL0\n"),
        1 => unsafe_puts("EL1\n"),
        2 => unsafe_puts("EL2\n"),
        3 => unsafe_puts("EL3\n"),
        _ => unsafe_puts("EL other\n"),
    }

    unsafe_puts("device_tree_base = 0x");
    unsafe_print_hex_u32(device_tree_base as u32);
    unsafe_puts("\n");

    // 2. Initialize the virtual memory.
    let vm = match initializer.init_virtual_memory() {
        Ok(vm) => vm,
        Err(msg) => {
            unsafe_puts("failed to initialize the virtual memory\n");
            unsafe_puts(msg);
            unsafe_puts("\n");
            wait_forever();
        }
    };

    let Some(ttbr0) = vm.get_ttbr0_addr() else {
        unsafe_puts("failed to get TTBR0_EL0\n");
        wait_forever();
    };

    write_volatile(&mut TTBR0_EL1, ttbr0);

    // 3. Start non-primary CPUs.
    write_volatile(&mut PRIMARY_READY, true);

    // 4. Enable MMU.
    super::vm::enable(ttbr0);

    unsafe_puts("The virtual memory has been successfully enabled.\n");

    awkernel_lib::arch::aarch64::init_primary(); // Initialize timer.

    // 5. Enable heap allocator.
    let backup_start = HEAP_START;
    let backup_size = BACKUP_HEAP_SIZE;
    let primary_start = HEAP_START + BACKUP_HEAP_SIZE;
    let primary_size = vm.get_heap_size().unwrap() - BACKUP_HEAP_SIZE;

    heap::init_primary(primary_start, primary_size);
    heap::init_backup(backup_start, backup_size);

    heap::TALLOC.use_primary_then_backup(); // use backup allocator

    // 6. Board specific initialization (Interrupt controller, etc).
    if let Err(msg) = initializer.init() {
        unsafe_puts("failed init()\n");
        unsafe_puts(msg);
        unsafe_puts("\n");
        wait_forever();
    }

    log::info!(
        "Primary heap: 0x{:016x} - {:016x} ({}[MiB])",
        primary_start,
        primary_start + primary_size,
        primary_size >> 20
    );

    log::info!(
        "Backup heap : 0x{:016x} - {:016x} ({}[MiB])",
        backup_start,
        backup_start + backup_size,
        backup_size >> 20
    );

    if awkernel_aarch64::spsel::get() & 1 == 0 {
        log::info!("Use SP_EL0.");
    } else {
        log::info!("Use SP_ELx.");
    }

    log::info!("Waking non-primary CPUs up.");
    PRIMARY_INITIALIZED.store(true, Ordering::SeqCst);

    wait_forever();

    // 2. Initialize the virtual memory.
    // mmu::init_memory_map();
    // if mmu::init().is_none() {
    //     unsafe_puts("Failed to init MMU.\n");
    //     wait_forever();
    // }

    // 3. Start non-primary CPUs.
    write_volatile(&mut PRIMARY_READY, true);

    // 4. Enable MMU.
    // mmu::enable();

    awkernel_lib::arch::aarch64::init_primary(); // Initialize timer.

    let backup_start = HEAP_START as usize;
    let backup_size = BACKUP_HEAP_SIZE as usize;
    let primary_start = (HEAP_START + BACKUP_HEAP_SIZE) as usize;
    let primary_size = HEAP_SIZE as usize;

    // 5. Enable heap allocator.
    heap::init_primary(primary_start, primary_size);
    heap::init_backup(backup_start, backup_size);
    heap::TALLOC.use_primary_then_backup(); // use backup allocator

    // 6. Board specific initialization.
    super::bsp::init();

    // log::info!(
    //     "Stack memory: start = 0x{:x}, end = 0x{:x}",
    //     get_stack_el1_end(),
    //     get_stack_el1_start()
    // );

    log::info!(
        "Primary heap: start = 0x{:x}, size = {}",
        primary_start,
        primary_size
    );

    log::info!(
        "Backup heap: start = 0x{:x}, size = {}",
        backup_start,
        backup_size
    );

    if awkernel_aarch64::spsel::get() & 1 == 0 {
        log::info!("Use SP_EL0.");
    } else {
        log::info!("Use SP_ELx.");
    }

    log::info!("Waking non-primary CPUs up.");
    PRIMARY_INITIALIZED.store(true, Ordering::SeqCst);

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: 0,
    };

    // TODO
    // log::info!("{}", tree);

    log::info!("device_tree_base: 0x{device_tree_base:x}");

    crate::main::<()>(kernel_info);
}

/// 1. Enable the virtual memory.
/// 2. Wait until the primary CPU is enabled.
/// 3. Initialization for non-primary CPUs.
unsafe fn non_primary_cpu() {
    // 1. Enable the virtual memory.
    let ttbr0 = read_volatile(&TTBR0_EL1);
    super::vm::enable(ttbr0);

    // 2. Wait until the primary CPU is enabled.
    while !PRIMARY_INITIALIZED.load(Ordering::SeqCst) {
        core::hint::spin_loop();
    }

    // 3. Initialization for non-primary CPUs.
    unsafe { awkernel_lib::arch::aarch64::init_non_primary() }; // Initialize timer.

    log::info!("non_primary_cpu()");
    loop {}

    awkernel_lib::interrupt::init_non_primary(); // Initialize the interrupt controller.

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: cpu::core_pos(),
    };

    heap::TALLOC.use_primary_then_backup(); // use backup allocator

    crate::main::<()>(kernel_info);
}

unsafe fn load_device_tree(
    device_tree_base: usize,
) -> &'static DeviceTree<'static, local_heap::LocalHeap<'static>> {
    if let Ok(tree) = awkernel_lib::device_tree::from_address(device_tree_base) {
        tree
    } else {
        unsafe_puts("kernel panic: failed to load the device tree\n");
        wait_forever();
    }
}
