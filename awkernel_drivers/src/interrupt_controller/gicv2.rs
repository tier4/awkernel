//! # IRQ Number
//!
//! | INTID            | Interrupt Type           | Notes                                        |
//! |------------------|--------------------------|----------------------------------------------|
//! | 0 - 15           | SGIs                     | Banked per PE                                |
//! | 16 - 31          | PPIs                     | Banked per PE                                |
//! | 32 - 1019        | SPIs                     |                                              |
//! | 1020 - 1023      | Special interrupt number | Used to signal special cases                 |

use alloc::boxed::Box;
use awkernel_lib::interrupt::InterruptController;
use core::default::Default;

const GIC_MAX_INTS: u16 = 1020;
const NUM_INTS_PER_REG: u16 = 32;

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

    // TargetListFilter
    pub const GIDG_SGIR_TARGET_LIST: u32 = 0b00;
    pub const GIDG_SGIR_TARGET_ALL_EXCEPT_SELF: u32 = 0b01 << 24;
    pub const _GIDG_SGIR_TARGET_SELF: u32 = 0b10 << 24;

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
    mmio_w! (offset 0xF00 => pub GICD_SGIR<u32>);
}

#[derive(Default)]
pub struct GICv2 {
    gicd_base: usize,
    gicc_base: usize,
    max_it: u16,
}

fn div_ceil(a: usize, b: usize) -> usize {
    (a + b - 1) / b
}

impl GICv2 {
    pub fn new(gicd_base: usize, gicc_base: usize) -> Self {
        let mut gic = GICv2 {
            gicd_base,
            gicc_base,
            max_it: 0,
        };

        // Disable the distributor.
        registers::GICD_CTLR.write(registers::GicdCtlrNonSecure::empty(), gicd_base);
        registers::GICC_CTLR.write(registers::GiccCtlrNonSecure::empty(), gicc_base);

        // Get the biggest IRQ#.
        gic.probe_max_it();

        for i in 0..div_ceil(gic.max_it as usize, NUM_INTS_PER_REG as usize) {
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
        for i in 0..div_ceil(gic.max_it as usize, 4) {
            let base = gicd_base + i * 4;

            if i < 8 {
                // GICD_ITARGETSR0 to GICD_ITARGETSR7 are read-only.
                registers::GICD_ITARGETSR.write(0x01010101, base);
            }

            registers::GICD_IPRIORITYR.write(0xa0a0a0a0, base);
        }

        // Config all interrupts to level triggered.
        // GICD_ICFGR0 is read-only.
        for i in 1..div_ceil(gic.max_it as usize, NUM_INTS_PER_REG as usize / 2) {
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
            let base = self.gicd_base + i as usize * 4;

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

    fn _set_priority(&self, irq: u16, priority: u8) {
        if irq > self.max_it {
            return;
        }

        let shift = (irq as u32 & 0b11) * 8;
        let mask = !(0xff << shift);
        let base = self.gicd_base + (irq as usize >> 2) * 4;

        let old_priority = registers::GICD_IPRIORITYR.read(base);

        registers::GICD_IPRIORITYR
            .write((old_priority & mask) | ((priority as u32) << shift), base);
    }

    fn _set_target_processor(&self, irq: u16, processor: u8) {
        if irq > self.max_it {
            return;
        }

        let base = self.gicd_base + (irq as usize >> 2) * 4;
        let target_shift = (irq & 0b11) * 8;

        let mut target = registers::GICD_ITARGETSR.read(base);
        target &= !(0xff << target_shift);
        target |= (1 << processor) << target_shift;

        registers::GICD_ITARGETSR.write(target, base);
    }

    fn iter(&self) -> PendingInterruptIterator {
        PendingInterruptIterator {
            gicc_base: self.gicc_base,
            done: false,
        }
    }
}

pub type IRQNumber = u16;

impl InterruptController for GICv2 {
    fn enable_irq(&mut self, irq: u16) {
        if irq > self.max_it {
            log::warn!(
                "GICv2: Failed to enable IRQ #{irq}, because it is greater than {}.",
                self.max_it
            );
            return;
        }

        let idx = irq >> 5;
        let mask = 1 << (irq & (NUM_INTS_PER_REG - 1)) as u32;
        let base = self.gicd_base + idx as usize * 4;

        registers::GICD_ISENABLER.write(mask, base);

        let cpu_id = awkernel_lib::cpu::cpu_id();

        log::info!("GICv2: IRQ #{irq} has been enabled on CPU#{cpu_id}.");
    }

    fn disable_irq(&mut self, irq: u16) {
        if irq > self.max_it {
            log::warn!(
                "GICv2: Failed to disable IRQ #{irq}, because it is greater than {}.",
                self.max_it
            );
            return;
        }

        let idx = irq >> 5;
        let mask = 1 << (irq & (NUM_INTS_PER_REG - 1)) as u32;
        let base = self.gicd_base + idx as usize * 4;

        registers::GICD_ICENABLER.write(mask, base);

        log::info!("GICv2: IRQ #{irq} has been disabled.");
    }

    fn pending_irqs(&self) -> Box<dyn Iterator<Item = u16>> {
        Box::new(self.iter())
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

    fn send_ipi(&mut self, irq: u16, target: u16) {
        let value =
            registers::GIDG_SGIR_TARGET_LIST | 1 << ((target & 0xff) + 16) | (irq as u32 & 0x0f);
        registers::GICD_SGIR.write(value, self.gicd_base);
    }

    fn send_ipi_broadcast(&mut self, irq: u16) {
        let value = registers::GIDG_SGIR_TARGET_LIST | (0xff << 16) | (irq as u32 & 0x0f);
        registers::GICD_SGIR.write(value, self.gicd_base);
    }

    fn send_ipi_broadcast_without_self(&mut self, irq: u16) {
        let value = registers::GIDG_SGIR_TARGET_ALL_EXCEPT_SELF | (irq as u32 & 0x0f);
        registers::GICD_SGIR.write(value, self.gicd_base);
    }

    fn irq_range(&self) -> (u16, u16) {
        (1, self.max_it)
    }

    fn irq_range_for_pnp(&self) -> (u16, u16) {
        (96, self.max_it)
    }
}

pub struct PendingInterruptIterator {
    gicc_base: usize,
    done: bool,
}

const ID_SPURIOUS: u16 = 1023;

impl Iterator for PendingInterruptIterator {
    type Item = u16;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        self.done = true;

        let iar = registers::GICC_IAR.read(self.gicc_base);
        registers::GICC_EOIR.write(iar, self.gicc_base);

        let id = iar as u16 & (1024 - 1);

        if id == ID_SPURIOUS {
            None
        } else {
            Some(id)
        }
    }
}
