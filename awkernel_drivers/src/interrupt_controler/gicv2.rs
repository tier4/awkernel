use awkernel_lib::interrupt::InterruptController;
use core::default::Default;

const GIC_MAX_INTS: usize = 1020;
const NUM_INTS_PER_REG: usize = 32;

mod registers {
    use awkernel_lib::{mmio_r, mmio_rw, mmio_w};
    use bitflags::bitflags;

    bitflags! {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct GiccCtlrNonSecure: u32 {
            const ENABLE_GRP1      = 0b0000_0000_0001;
            const FIQ_BYP_DIS_GRP1 = 0b0000_0010_0000;
            const IRQ_BYP_DIS_GRP1 = 0b0000_0100_0000;
            const EOI_MODE_NS      = 0b0010_0000_0000;
        }

        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct GicdCtlrNonSecure: u32 {
            const ENABLE           = 0b0000_0000_0001;
        }
    }

    mmio_rw!(offset 0x000 => pub GICC_CTLR<GiccCtlrNonSecure>);
    mmio_rw!(offset 0x004 => pub GICC_PMR<u32>);
    mmio_r! (offset 0x00C => pub GICC_IAR<u32>);
    mmio_w! (offset 0x010 => pub GICC_EOIR<u32>);

    mmio_rw!(offset 0x000 => pub GICD_CTLR<GicdCtlrNonSecure>);
    mmio_rw!(offset 0x080 => pub GICD_IGROUPR<u32>);
    mmio_rw!(offset 0x100 => pub GICD_ISENABLER<u32>);
    mmio_rw!(offset 0x180 => pub GICD_ICENABLER<u32>);
    mmio_rw!(offset 0x280 => pub GICD_ICPENDR<u32>);
    mmio_rw!(offset 0x380 => pub GICD_ICACTIVER<u32>);
    mmio_rw!(offset 0x400 => pub GICD_IPRIORITYR<u32>);
    mmio_rw!(offset 0x800 => pub GICD_ITARGETSR<u32>);
    mmio_rw!(offset 0xc00 => pub GICD_ICFGR<u32>);
}

#[derive(Default)]
pub struct GICv2 {
    gicc_base: usize,
    gicd_base: usize,
    max_it: usize,
    iter: Option<PendingInterruptIterator>,
}

fn div_ceil(a: usize, b: usize) -> usize {
    (a + b - 1) / b
}

impl GICv2 {
    pub fn new(gicc_base: usize, gicd_base: usize) -> Self {
        let mut gic = GICv2 {
            gicc_base,
            gicd_base,
            max_it: 0,
            iter: None,
        };

        // Disable the distributor.
        registers::GICD_CTLR.write(registers::GicdCtlrNonSecure::empty(), gicd_base);
        registers::GICC_CTLR.write(registers::GiccCtlrNonSecure::empty(), gicc_base);

        // Get the maximum number of interrupt.
        gic.probe_max_it();

        log::info!("GICv2: The number of interrupts is {}.", gic.max_it);

        for i in 0..div_ceil(gic.max_it, NUM_INTS_PER_REG) {
            let base = gicd_base + i * 4;

            // Disable interrupts.
            registers::GICD_ICENABLER.write(!0, base);

            // Make interrupts non-pending.
            registers::GICD_ICPENDR.write(!0, base);

            // Make interrupts group 1.
            registers::GICD_IGROUPR.write(!0, base);

            // Deactivates interrupts.
            registers::GICD_ICACTIVER.write(!0, base);
        }

        // Direct all interrupts to core 0 (=01) with default priority a0.
        for i in 0..div_ceil(gic.max_it, 4) {
            let base = gicd_base + i * 4;

            if i < 8 {
                // GICD_ITARGETSR0 to GICD_ITARGETSR7 are read-only.
                registers::GICD_ITARGETSR.write(0x01010101, base);
            }

            registers::GICD_IPRIORITYR.write(0xa0a0a0a0, base);
        }

        // Config all interrupts to level triggered.
        // GICD_ICFGR0 is read-only.
        for i in 1..div_ceil(gic.max_it, NUM_INTS_PER_REG / 2) {
            let base = gicd_base + i * 4;
            registers::GICD_ICFGR.write(0, base);
        }

        // Enable the distributor.
        registers::GICD_CTLR.write(registers::GicdCtlrNonSecure::ENABLE, gicd_base);

        // Mask interrupts whose priority is greater than 0x80.
        registers::GICC_PMR.write(0xF0, gicc_base);

        // Enable the CPU interface.
        registers::GICC_CTLR.write(registers::GiccCtlrNonSecure::ENABLE_GRP1, gicc_base);

        gic
    }

    fn probe_max_it(&mut self) {
        let max_regs = ((GIC_MAX_INTS + NUM_INTS_PER_REG - 1) >> 5) - 1;
        let old_ctlr = registers::GICC_CTLR.read(self.gicc_base);
        registers::GICC_CTLR.write(registers::GiccCtlrNonSecure::empty(), self.gicc_base);

        for i in (0..=max_regs).rev() {
            let base = self.gicd_base + i * 4;

            let old_reg = registers::GICD_ISENABLER.read(base);
            registers::GICD_ISENABLER.write(!0, base);

            let reg = registers::GICD_ISENABLER.read(base);
            registers::GICD_ICENABLER.write(!old_reg, base);

            for b in (0..NUM_INTS_PER_REG).rev() {
                if (1 << b) & reg > 0 {
                    self.max_it = i * NUM_INTS_PER_REG + b;
                    registers::GICC_CTLR.write(old_ctlr, self.gicc_base);
                    return;
                }
            }
        }

        self.max_it = NUM_INTS_PER_REG * max_regs;
        registers::GICC_CTLR.write(old_ctlr, self.gicc_base);
    }

    fn _set_priority(&self, irq: usize, priority: u8) {
        if irq > self.max_it {
            return;
        }

        let shift = (irq as u32 & 0b11) * 8;
        let mask = !(0xff << shift);
        let base = self.gicd_base + (irq >> 2) * 4;

        let old_priority = registers::GICD_IPRIORITYR.read(base);

        registers::GICD_IPRIORITYR
            .write((old_priority & mask) | ((priority as u32) << shift), base);
    }

    fn _set_target_processor(&self, irq: usize, processor: u8) {
        if irq > self.max_it {
            return;
        }

        let base = self.gicd_base + (irq >> 2) * 4;
        let target_shift = (irq & 0b11) * 8;

        let mut target = registers::GICD_ITARGETSR.read(base);
        target &= !(0xff << target_shift);
        target |= (1 << processor) << target_shift;

        registers::GICD_ITARGETSR.write(target, base);
    }

    fn iter(&mut self) -> PendingInterruptIterator {
        PendingInterruptIterator {
            gicc_base: self.gicc_base,
            done: false,
        }
    }
}

pub type IRQNumber = u16;

impl InterruptController for GICv2 {
    fn enable_irq(&mut self, irq: usize) {
        if irq > self.max_it {
            log::warn!(
                "GICv2: Failed to enable IRQ #{irq}, because it is greater than {}.",
                self.max_it
            );
            return;
        }

        let idx = irq >> 5;
        let mask = 1 << (irq & (NUM_INTS_PER_REG - 1)) as u32;
        let base = self.gicd_base + idx * 4;

        registers::GICD_ISENABLER.write(mask, base);

        log::info!("GICv2: IRQ #{irq} has been enabled.");
    }

    fn disable_irq(&mut self, irq: usize) {
        if irq > self.max_it {
            log::warn!(
                "GICv2: Failed to disable IRQ #{irq}, because it is greater than {}.",
                self.max_it
            );
            return;
        }

        let idx = irq >> 5;
        let mask = 1 << (irq & (NUM_INTS_PER_REG - 1)) as u32;
        let base = self.gicd_base + idx * 4;

        registers::GICD_ICENABLER.write(mask, base);

        log::info!("GICv2: IRQ #{irq} has been disabled.");
    }

    fn pending_irqs(&mut self) -> &mut dyn Iterator<Item = usize> {
        self.iter = Some(self.iter());
        self.iter.as_mut().unwrap()
    }

    fn init_non_primary(&mut self) {
        // Disable.
        registers::GICC_CTLR.write(registers::GiccCtlrNonSecure::empty(), self.gicc_base);

        // Disable interrupts.
        registers::GICD_ICENABLER.write(!0, self.gicd_base);

        // Make interrupts non-pending.
        registers::GICD_ICPENDR.write(!0, self.gicd_base);

        // Make interrupts group 1.
        registers::GICD_IGROUPR.write(!0, self.gicd_base);

        // Deactivates interrupts.
        registers::GICD_ICACTIVER.write(!0, self.gicd_base);

        // Default priority is a0.
        for i in 0..8 {
            registers::GICD_IPRIORITYR.write(0xa0a0a0a0, self.gicd_base + 4 * i);
        }

        // Mask interrupts whose priority is greater than 0x80.
        registers::GICC_PMR.write(0xF0, self.gicc_base);

        // Enable the CPU interface.
        registers::GICC_CTLR.write(registers::GiccCtlrNonSecure::ENABLE_GRP1, self.gicc_base);
    }

    fn send_ipi(&mut self, irq: usize, target: usize) {
        todo!()
    }

    fn send_ipi_broadcast(&mut self, irq: usize) {
        todo!()
    }

    fn send_ipi_broadcast_without_self(&mut self, irq: usize) {
        todo!()
    }
}

pub struct PendingInterruptIterator {
    gicc_base: usize,
    done: bool,
}

const ID_SPURIOUS: u32 = 1023;

impl Iterator for PendingInterruptIterator {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let iar = registers::GICC_IAR.read(self.gicc_base);
        registers::GICC_EOIR.write(iar, self.gicc_base);

        let id = iar & (1024 - 1);

        self.done = true;

        if id == ID_SPURIOUS {
            None
        } else {
            Some(id as usize)
        }
    }
}
