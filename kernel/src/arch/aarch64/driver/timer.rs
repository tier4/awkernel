use crate::arch::aarch64::bsp::memory::MMIO_BASE;
use awkernel_lib::interrupt;

mod registers {
    use awkernel_lib::{mmio_r, mmio_w};

    mmio_w!(offset 0x00 => pub CONTROL<u32>);
    mmio_r!(offset 0x04 => pub COUNT_LOW<u32>);
    mmio_w!(offset 0x10 => pub COMPARE_1<u32>);
}

const BASE: usize = MMIO_BASE + 0x3000;

pub struct SystemTimer;

impl SystemTimer {
    pub fn init(irq: usize) {
        log::info!("timer: initializing generic arm timer to trigger context switch");

        interrupt::register_handler(irq, SystemTimer::handle_irq).unwrap();
        interrupt::enable_irq(irq);

        let value = registers::COUNT_LOW.read(BASE) + 2000000;
        registers::COMPARE_1.write(value, BASE);
    }

    pub fn reset() {
        registers::CONTROL.write(1 << 1, BASE);
        let value = registers::COUNT_LOW.read(BASE) + 2000000;
        registers::COMPARE_1.write(value, BASE);
    }

    fn handle_irq() {
        log::info!("handle timer");
        SystemTimer::reset();
    }
}
