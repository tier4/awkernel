//! # Boot process
//!
//! ## Raspberry Pi
//!
//! 1. The entrypoint, `_start` in `kernel/asm/aarch64/device/raspi.S`, is called.
//! 2. [`kernel_main`] is called.
//! 3. For the primary CPU, [`primary_cpu`] is called and some initializations are performed.
//! 4. For non-primary CPUs, [`non_primary_cpu`] is called.

use super::{bsp::raspi, console, cpu, driver::uart::DevUART, mmu};
use crate::{
    arch::aarch64::{
        cpu::{CLUSTER_COUNT, MAX_CPUS_PER_CLUSTER},
        driver::timer::SystemTimer,
        mmu::{get_stack_el1_end, get_stack_el1_start},
    },
    config::{BACKUP_HEAP_SIZE, HEAP_SIZE, HEAP_START},
    kernel_info::KernelInfo,
};
use awkernel_lib::{delay::wait_forever, heap, interrupt, serial::Serial};
use core::{
    ptr::{read_volatile, write_volatile},
    sync::atomic::{AtomicBool, Ordering},
};
use raspi::memory::{DEVICE_MEM_END, DEVICE_MEM_START};

static mut PRIMARY_READY: bool = false;
static PRIMARY_INITIALIZED: AtomicBool = AtomicBool::new(false);

/// Entry point from assembly code.
#[no_mangle]
pub unsafe extern "C" fn kernel_main() -> ! {
    awkernel_aarch64::init_cpacr_el1(); // Enable floating point numbers.

    if cpu::core_pos() == 0 {
        raspi::start_non_primary(); // Wake non-primary CPUs up.
        primary_cpu();
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
/// 5. Enable serial port.
unsafe fn primary_cpu() {
    // Initialize UART.
    console::init_device();

    match awkernel_aarch64::get_current_el() {
        0 => DevUART::raw_puts("EL0\n"),
        1 => DevUART::raw_puts("EL1\n"),
        2 => DevUART::raw_puts("EL2\n"),
        3 => DevUART::raw_puts("EL3\n"),
        _ => (),
    }

    // 1. Initialize MMU.
    mmu::init_memory_map();
    if mmu::init().is_none() {
        DevUART::raw_puts("Failed to init MMU.\n");
        wait_forever();
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

    // 5. Enable serial port.
    console::init();

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

    // Board specific initialization.
    super::bsp::init();

    interrupt::enable_irq(121 + 32); // Enable UART0

    interrupt::enable();

    loop {}

    log::info!("Waking non-primary CPUs up.");
    PRIMARY_INITIALIZED.store(true, Ordering::SeqCst);

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: 0,
    };
    crate::main::<()>(kernel_info);
}

unsafe fn non_primary_cpu() {
    mmu::enable();

    while !PRIMARY_INITIALIZED.load(Ordering::SeqCst) {
        core::hint::spin_loop();
    }

    unsafe { awkernel_lib::arch::aarch64::init_non_primary() }; // Initialize timer.

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: cpu::core_pos(),
    };

    heap::TALLOC.use_primary_then_backup(); // use backup allocator

    crate::main::<()>(kernel_info);
}
