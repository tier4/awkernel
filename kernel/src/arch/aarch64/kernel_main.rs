use super::{
    cpu,
    driver::uart::{DevUART, UART},
    mmu, serial,
};
use crate::{arch::Delay, heap, kernel_info::KernelInfo};
use core::fmt::Write;

/// entry point from assembly code
#[no_mangle]
pub extern "C" fn kernel_main() -> ! {
    if cpu::core_pos() == 0 {
        primary_cpu();
    } else {
        cpu::wait_event(); // Wait non-primary CPU.
        non_primary_cpu();
    }

    super::delay::ArchDelay::wait_forever();
}

fn primary_cpu() {
    mmu::init_memory_map();

    if mmu::init().is_none() {
        let mut serial = DevUART::new(super::bsp::memory::UART0_BASE);
        serial.init(serial::UART_CLOCK, serial::UART_BAUD);
        let _ = serial.write_str("Failed to init MMU.\n");
        loop {}
    }

    heap::init(); // Enable heap allocator.
    serial::init(); // Enable serial port.
    cpu::init_cpacr_el1(); // Enable floating point numbers.
    cpu::start_non_primary(); // Wake non-primary CPUs up.

    cpu::send_event(); // Start non-primary CPUs.

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: 0,
    };

    crate::main::<()>(kernel_info);
}

fn non_primary_cpu() {
    mmu::set_regs();

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: cpu::core_pos(),
    };

    crate::main::<()>(kernel_info);
}
