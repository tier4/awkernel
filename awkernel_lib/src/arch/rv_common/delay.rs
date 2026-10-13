use super::{interrupt_controller, ArchImpl};
use crate::delay::Delay;

impl Delay for ArchImpl {
    #[inline]
    fn wait_interrupt() {
        riscv::asm::wfi();
    }

    #[inline]
    fn wait_microsec(usec: u64) {
        interrupt_controller::clint().wait_usec(usec);
    }

    #[inline]
    fn uptime() -> u64 {
        interrupt_controller::clint().uptime_us()
    }

    #[inline]
    fn uptime_nano() -> u128 {
        interrupt_controller::clint().uptime_nano()
    }

    #[inline]
    fn cpu_counter() -> u64 {
        riscv::register::cycle::read64()
    }
}
