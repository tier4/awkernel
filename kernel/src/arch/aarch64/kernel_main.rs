use super::{
    bsp::raspi,
    cpu,
    driver::uart::{DevUART, Uart},
    mmu, serial,
};
use crate::{heap, kernel_info::KernelInfo};
use core::{
    ptr::{read_volatile, write_volatile},
    sync::atomic::{AtomicBool, Ordering},
};
use t4os_lib::delay::wait_forever;

static mut PRIMARY_READY: bool = false;
static PRIMARY_INITIALIZED: AtomicBool = AtomicBool::new(false);

/// Entry point from assembly code.
#[no_mangle]
pub extern "C" fn kernel_main() -> ! {
    t4os_aarch64::init_cpacr_el1(); // Enable floating point numbers.

    if cpu::core_pos() == 0 {
        raspi::start_non_primary(); // Wake non-primary CPUs up.
        primary_cpu();
    } else {
        while !unsafe { read_volatile(&PRIMARY_READY) } {}
        non_primary_cpu();
    }

    wait_forever();
}

fn primary_cpu() {
    DevUART::init(serial::UART_CLOCK, serial::UART_BAUD);

    match t4os_aarch64::get_current_el() {
        0 => unsafe { DevUART::unsafe_puts("EL0\n") },
        1 => unsafe { DevUART::unsafe_puts("EL1\n") },
        2 => unsafe { DevUART::unsafe_puts("EL2\n") },
        3 => unsafe { DevUART::unsafe_puts("EL3\n") },
        _ => (),
    }

    // Initialize MMU.
    mmu::init_memory();
    if mmu::init().is_none() {
        unsafe { DevUART::unsafe_puts("Failed to init MMU.\n") };
        wait_forever();
    }

    // Start non-primary CPUs.
    unsafe { write_volatile(&mut PRIMARY_READY, true) };

    // Enable MMU.
    mmu::enable();

    t4os_lib::arch::aarch64::init_primary(); // Initialize timer.
    heap::init(); // Enable heap allocator.
    serial::init(); // Enable serial port.

    PRIMARY_INITIALIZED.store(true, Ordering::SeqCst);

    log::info!("Waking non-primary CPUs up.");

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: 0,
    };

    crate::main::<()>(kernel_info);
}

fn non_primary_cpu() {
    mmu::enable();

    while !PRIMARY_INITIALIZED.load(Ordering::SeqCst) {
        core::hint::spin_loop();
    }

    t4os_lib::arch::aarch64::init_non_primary(); // Initialize timer.

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: cpu::core_pos(),
    };

    t4os_aarch64::init_cpacr_el1(); // Enable floating point numbers.

    crate::main::<()>(kernel_info);
}
