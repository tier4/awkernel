use super::{
    cpu, delay,
    driver::uart::{DevUART, UART},
    mmu, serial,
};
use crate::{delay::Delay, heap, kernel_info::KernelInfo};
use core::{
    ptr::{read_volatile, write_volatile},
    sync::atomic::{AtomicBool, Ordering},
};

static mut PRIMARY_READY: bool = false;
static PRIMARY_INITIALIZED: AtomicBool = AtomicBool::new(false);

/// Entry point from assembly code.
#[no_mangle]
pub extern "C" fn kernel_main() -> ! {
    if cpu::core_pos() == 0 {
        cpu::start_non_primary(); // Wake non-primary CPUs up.
        primary_cpu();
    } else {
        while !unsafe { read_volatile(&PRIMARY_READY) } {}
        non_primary_cpu();
    }

    super::delay::ArchDelay::wait_forever();
}

fn primary_cpu() {
    DevUART::init(serial::UART_CLOCK, serial::UART_BAUD);

    match cpu::get_current_el() {
        0 => unsafe { DevUART::unsafe_puts("EL0\n") },
        1 => unsafe { DevUART::unsafe_puts("EL1\n") },
        2 => unsafe { DevUART::unsafe_puts("EL2\n") },
        3 => unsafe { DevUART::unsafe_puts("EL3\n") },
        _ => (),
    }

    // Initialize MMU.
    mmu::init_memory_map();
    if mmu::init().is_none() {
        unsafe { DevUART::unsafe_puts("Failed to init MMU.\n") };
        loop {}
    }

    // Start non-primary CPUs.
    unsafe { write_volatile(&mut PRIMARY_READY, true) };

    // Enable MMU.
    mmu::enable();

    delay::init(); // Initialize timer.
    heap::init(); // Enable heap allocator.
    serial::init(); // Enable serial port.
    cpu::init_cpacr_el1(); // Enable floating point numbers.

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

    while !PRIMARY_INITIALIZED.load(Ordering::SeqCst) {}

    delay::ArchDelay::wait_millisec(100);

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: cpu::core_pos(),
    };

    cpu::init_cpacr_el1(); // Enable floating point numbers.

    crate::main::<()>(kernel_info);
}
