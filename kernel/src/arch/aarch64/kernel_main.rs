//! # Boot process
//!
//! ## Raspberry Pi
//!
//! 1. The entrypoint, `_start` in `kernel/asm/aarch64/device/raspi.S`, is called.
//! 2. [`kernel_main`] is called.
//! 3. For the primary CPU, [`primary_cpu`] is called and some initializations are performed.
//! 4. For non-primary CPUs, [`non_primary_cpu`] is called.

use super::{bsp::raspi, cpu, mmu};
use crate::{
    arch::aarch64::{
        cpu::{CLUSTER_COUNT, MAX_CPUS_PER_CLUSTER},
        mmu::{get_stack_el1_end, get_stack_el1_start},
    },
    config::{BACKUP_HEAP_SIZE, HEAP_SIZE, HEAP_START},
    kernel_info::KernelInfo,
};
use awkernel_lib::{
    console::{unsafe_print_hex_u64, unsafe_puts},
    delay::wait_forever,
    device_tree::device_tree::DeviceTree,
    heap, local_heap,
};
use core::{
    ptr::{read_volatile, write_volatile},
    sync::atomic::{AtomicBool, Ordering},
};
use raspi::memory::{DEVICE_MEM_END, DEVICE_MEM_START};

static mut PRIMARY_READY: bool = false;
static PRIMARY_INITIALIZED: AtomicBool = AtomicBool::new(false);

/// Entry point from assembly code.
#[no_mangle]
pub unsafe extern "C" fn kernel_main(device_tree_base: usize) -> ! {
    awkernel_aarch64::init_cpacr_el1(); // Enable floating point numbers.

    awkernel_lib::delay::wait_millisec(10);

    if cpu::core_pos() == 0 {
        raspi::start_non_primary(); // Wake non-primary CPUs up.
        primary_cpu(device_tree_base);
    } else {
        while !unsafe { read_volatile(&PRIMARY_READY) } {}
        non_primary_cpu();
    }

    wait_forever();
}

/// 1. Initialize MMU.
/// 2. Start non-primary CPUs.
/// 3. Enable MMU.
/// 4. Enable heap allocator.
/// 5. Board specific initialization (IRQ controller, etc).
unsafe fn primary_cpu(device_tree_base: usize) {
    let device_tree = load_device_tree(device_tree_base);

    // Initialize UART.
    super::bsp::init_device(device_tree);

    unsafe_puts("device_tree_base = 0x");
    unsafe_print_hex_u64(device_tree_base as u64);
    unsafe_puts("\n");

    let magic_number = read_volatile(device_tree_base as *const u32);
    let total_size = read_volatile((device_tree_base + 4) as *const u32);

    unsafe_puts("magic_number = 0x");
    unsafe_print_hex_u64(u32::from_be(magic_number as u32) as u64);
    unsafe_puts("\n");
    unsafe_puts("total_size = 0x");
    unsafe_print_hex_u64(u32::from_be(total_size as u32) as u64);
    unsafe_puts("\n");

    unsafe_puts("loaded the device tree\n");

    awkernel_lib::device_tree::print_device_tree_node(device_tree.root(), 0);

    // 1. Initialize MMU.
    mmu::init_memory_map();
    if mmu::init().is_none() {
        unsafe_puts("Failed to init MMU.\n");
        wait_forever();
    }

    // awkernel_lib::delay::wait_millisec(2000);

    // Read the device tree.
    // let dtb: &[u8] = include_bytes!("../../../../bcm2710-rpi-3-b-plus.dtb");
    // let Ok(tree) = awkernel_lib::device_tree::from_bytes(dtb) else {
    //     // unsafe_puts("kernel panic: failed to load the device tree\n");
    // wait_forever();
    // };

    match awkernel_aarch64::get_current_el() {
        0 => unsafe_puts("EL0\n"),
        1 => unsafe_puts("EL1\n"),
        2 => unsafe_puts("EL2\n"),
        3 => unsafe_puts("EL3\n"),
        _ => (),
    }

    // 2. Start non-primary CPUs.
    write_volatile(&mut PRIMARY_READY, true);

    // 3. Enable MMU.
    mmu::enable();

    awkernel_lib::arch::aarch64::init_primary(); // Initialize timer.
    awkernel_lib::arch::aarch64::set_cluster_info(MAX_CPUS_PER_CLUSTER, CLUSTER_COUNT);

    let backup_start = HEAP_START as usize;
    let backup_size = BACKUP_HEAP_SIZE as usize;
    let primary_start = (HEAP_START + BACKUP_HEAP_SIZE) as usize;
    let primary_size = HEAP_SIZE as usize;

    // 4. Enable heap allocator.
    heap::init_primary(primary_start, primary_size);
    heap::init_backup(backup_start, backup_size);
    heap::TALLOC.use_primary_then_backup(); // use backup allocator

    // 5. Board specific initialization.
    super::bsp::init();

    log::info!(
        "Stack memory: start = 0x{:x}, end = 0x{:x}",
        get_stack_el1_end(),
        get_stack_el1_start()
    );

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

    log::info!(
        "Device memory: start = 0x{:x}, end = 0x{:x}",
        DEVICE_MEM_START,
        DEVICE_MEM_END
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

unsafe fn non_primary_cpu() {
    mmu::enable();

    while !PRIMARY_INITIALIZED.load(Ordering::SeqCst) {
        core::hint::spin_loop();
    }

    unsafe { awkernel_lib::arch::aarch64::init_non_primary() }; // Initialize timer.

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
    const MAGIC: u32 = 0xd00d_feed;

    let magic_number = read_volatile(device_tree_base as *const u32);
    let total_size = read_volatile((device_tree_base + 4) as *const u32);

    let magic_number = u32::from_be(magic_number);

    if magic_number != MAGIC {
        unsafe_puts("kernel panic: failed to load the device tree.\n");
        wait_forever();
    }

    let total_size = u32::from_be(total_size);

    let dtb = core::slice::from_raw_parts(device_tree_base as *const u8, total_size as usize);

    unsafe {
        unsafe_puts("hello world\n");
    }

    let Ok(tree) = awkernel_lib::device_tree::from_bytes(dtb) else {
        unsafe_puts("kernel panic: failed to parse the device tree\n");
        wait_forever();
    };

    tree
}
