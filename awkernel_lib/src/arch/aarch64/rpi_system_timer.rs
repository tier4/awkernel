mod registers {
    use crate::{mmio_r, mmio_w};

    mmio_w!(offset 0x00 => pub CONTROL<u32>);
    mmio_r!(offset 0x04 => pub COUNT_LOW<u32>);
    mmio_w!(offset 0x10 => pub COMPARE_1<u32>);
}

const PERIOD: u32 = 1000; // micro second

pub struct RpiSystemTimer {
    irq: usize,
    base: usize,
}

impl RpiSystemTimer {
    pub const fn new(irq: usize, base: usize) -> Self {
        RpiSystemTimer { irq, base }
    }
}

impl crate::timer::Timer for RpiSystemTimer {
    fn reset(&self) {
        registers::CONTROL.write(1 << 1, self.base);
        let value = registers::COUNT_LOW.read(self.base) + PERIOD;
        registers::COMPARE_1.write(value, self.base);
    }

    fn disable(&self) {
        registers::CONTROL.write(1 << 1, self.base);
    }

    fn irq_id(&self) -> usize {
        self.irq
    }
}
