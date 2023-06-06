use alloc::boxed::Box;
use awkernel_lib::{console::register_console, interrupt::register_interrupt_controller};
use core::arch::asm;

use crate::arch::aarch64::driver::uart;

use self::config::UART_IRQ;

pub mod config;
pub mod memory;

pub fn start_non_primary() {
    if cfg!(feature = "raspi3") {
        unsafe {
            asm!(
                "mov {0}, #0xe0
                 ldr {1}, =_start
                 str {1}, [{0}]     // core #1
                 str {1}, [{0},  8] // core #2
                 str {1}, [{0}, 16] // core #3",
            lateout(reg) _,
            lateout(reg) _
            );
        }
    }
}

#[cfg(feature = "raspi4")]
mod timer {
    use awkernel_lib::arch::aarch64::arm_timer::ArmTimer;
    pub static TIMER: ArmTimer = ArmTimer::new(30);
}

#[cfg(feature = "raspi4")]
pub fn init() {
    init_uart();

    // Set-up the interrupt controller.
    let gic = awkernel_drivers::interrupt_controler::gicv2::GICv2::new(
        memory::GIC_V2_CPU_INTERFACE_BASE,
        memory::GIC_V2_DISTRIBUTOR_BASE,
    );
    register_interrupt_controller(Box::new(gic));

    // Set-up timer.
    awkernel_lib::timer::register_timer(&timer::TIMER);
}

#[cfg(feature = "raspi3")]
mod timer {
    use awkernel_lib::arch::aarch64::rpi_system_timer::RpiSystemTimer;

    use super::memory::MMIO_BASE;
    pub static TIMER: RpiSystemTimer = RpiSystemTimer::new(1, MMIO_BASE + 0x3000);
}

#[cfg(feature = "raspi3")]
pub fn init() {
    // Set-up the interrupt controller.
    let ctrl = awkernel_drivers::interrupt_controler::bcm2835::BCM2835IntCtrl::new(
        memory::INTERRUPT_CTRL_BASE,
    );
    register_interrupt_controller(Box::new(ctrl));

    // Set-up timer.
    awkernel_lib::timer::register_timer(&timer::TIMER);
}

fn init_uart() {
    let port = Box::new(uart::pl011::PL011::new(UART_IRQ));
    register_console(port);

    // let _ = log::set_logger(&CONSOLE);
    // log::set_max_level(log::LevelFilter::Debug);
}

pub unsafe fn init_device() {
    uart::init_device();
    awkernel_lib::console::register_unsafe_puts(uart::unsafe_puts);
}
