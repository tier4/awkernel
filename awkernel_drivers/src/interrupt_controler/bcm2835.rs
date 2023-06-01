use awkernel_lib::interrupt::InterruptController;

mod registers {
    use awkernel_lib::{mmio_r, mmio_w};

    mmio_r!(offset 0x00 => pub IRQ_BASIC_PENDING<u32>);
    mmio_r!(offset 0x04 => pub IRQ_PENDING1<u32>);
    mmio_r!(offset 0x08 => pub IRQ_PENDING2<u32>);
    mmio_r!(offset 0x0C => pub FIQ_CONTROL<u32>);
    mmio_w!(offset 0x10 => pub IRQ_ENABLE1<u32>);
    mmio_w!(offset 0x14 => pub IRQ_ENABLE2<u32>);
    mmio_w!(offset 0x18 => pub IRQ_ENABLE_BASIC<u32>);
    mmio_w!(offset 0x1C => pub IRQ_DISABLE1<u32>);
    mmio_w!(offset 0x20 => pub IRQ_DISABLE2<u32>);
    mmio_w!(offset 0x24 => pub IRQ_DISABLE_BASIC<u32>);
}

pub struct BCM2835IntCtrl {
    iter: Option<PendingInterruptIterator>,
    base: usize,
}

impl BCM2835IntCtrl {
    pub fn new(base: usize) -> Self {
        log::info!("BCM2835 IRQ: Initializing the interrupt controller.");

        let gic = Self { base, iter: None };

        registers::IRQ_DISABLE1.write(!0, base);
        registers::IRQ_DISABLE2.write(!0, base);
        registers::IRQ_ENABLE_BASIC.write(!0, base);
        registers::IRQ_PENDING1.read(base);
        registers::IRQ_PENDING2.read(base);

        gic
    }

    pub fn iter(&mut self) -> PendingInterruptIterator {
        let pending = [
            registers::IRQ_PENDING1.read(self.base),
            registers::IRQ_PENDING2.read(self.base),
        ];

        PendingInterruptIterator { next: 0, pending }
    }
}

impl InterruptController for BCM2835IntCtrl {
    fn enable_irq(&mut self, irq: usize) {
        if irq >= 64 {
            log::warn!("BCM2835 IRQ: Failed to enable IRQ #{irq} because it is greater than 63.");
            return;
        } else if irq < 32 {
            registers::IRQ_ENABLE1.write(1 << irq, self.base);
        } else {
            registers::IRQ_ENABLE2.write(1 << (irq - 32), self.base);
        }

        log::info!("BCM2835 IRQ: IRQ #{irq} has been enabled.");
    }

    fn disable_irq(&mut self, irq: usize) {
        if irq >= 64 {
            log::warn!("BCM2835 IRQ: Failed to disable IRQ #{irq} because it is greater than 63.");
            return;
        } else if irq < 32 {
            registers::IRQ_DISABLE1.write(1 << irq, self.base);
        } else {
            registers::IRQ_DISABLE2.write(1 << (irq - 32), self.base);
        }

        log::info!("BCM2835 IRQ: IRQ #{irq} has been disabled.");
    }

    fn pending_irqs(&mut self) -> &mut dyn Iterator<Item = usize> {
        self.iter = Some(self.iter());
        self.iter.as_mut().unwrap()
    }
}

pub struct PendingInterruptIterator {
    next: usize,
    pending: [u32; 2],
}

impl Iterator for PendingInterruptIterator {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        let (mut index, mut bit) = if self.next < 32 {
            (0, self.next)
        } else {
            (1, self.next - 32)
        };

        while self.pending[index] & (1 << bit) == 0 {
            bit += 1;
            if bit >= 32 {
                bit = 0;
                index += 1;
                if index >= 2 {
                    return None;
                }
            }
        }

        self.next = index * 32 + bit + 1;
        Some(index * 32 + bit)
    }
}
