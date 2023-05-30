use awkernel_lib::interrupt;


mod registers {
    use awkernel_lib::{mmio_r, mmio_w};

    mmio_w!(offset 0x00 => pub CONTROL<u32>);
    mmio_r!(offset 0x04 => pub COUNT_LOW<u32>);
    mmio_w!(offset 0x10 => pub COMPARE_1<u32>);
}

pub const MMIO_BASE: usize = 0x3F000000;

pub struct SystemTimer;

impl SystemTimer {

    pub fn init(irq: usize) {
        log::info!("timer: initializing generic arm timer to trigger context switch");

        interrupt::register_irq(irq ,SystemTimer::handle_irq).unwrap();
        interrupt::enable_irq(irq);

            let value = registers::COUNT_LOW.read(MMIO_BASE + 0xB200)+ 20000;
            registers::COMPARE_1.write(value, MMIO_BASE + 0xB200);
            log::info!("20ms passed");

    }

    pub fn reset() {
        registers::CONTROL.write(1 << 1, MMIO_BASE + 0xB200);
        let value = registers::COUNT_LOW.read(MMIO_BASE + 0xB200) + 20000;
        registers::COMPARE_1.write(value, MMIO_BASE + 0xB200);
        
        log::info!("20ms passed");
    }

    fn handle_irq() {
        log::info!("handle timer");
        SystemTimer::reset();
    }
}