//! # IRQ Number
//!
//! | INTID            | Interrupt Type           | Notes                                        |
//! |------------------|--------------------------|----------------------------------------------|
//! | 0 - 15           | SGIs                     | Banked per PE                                |
//! | 16 - 31          | PPIs                     | Banked per PE                                |
//! | 32 - 1019        | SPIs                     |                                              |
//! | 1020 - 1023      | Special interrupt number | Used to signal special cases                 |
//! | 1024 - 8191      | Reserved LPIs            |                                              |
//! | 8192 and greater | LPIs                     | The upper boundary is IMPLEMENTATION DEFINED |

use alloc::boxed::Box;
use awkernel_lib::interrupt::InterruptController;

const NUM_INTS_PER_REG: u16 = 32;

mod registers {
    use awkernel_lib::{mmio_rw, mmio_w};
    use bitflags::bitflags;

    bitflags! {
        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        pub struct GicdCtlr: u32 {
            const RWP = 1 << 31;
            const nASSGIreq = 1 << 8;
            const E1NWF = 1 << 7;
            const DS = 1 << 6;
            const ARE_NS = 1 << 5;
            const ARE_S = 1 << 4;
            const EnableGrp1S = 1 << 2;
            const EnableGrp1NS = 1 << 1;
            const EnableGrp0 = 1 << 0;
        }

        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        pub struct GicrCtlr: u32 {
            const UWP = 1 << 31;
            const DPG1S = 1 << 26;
            const DPG1NS = 1 << 25;
            const DPG0 = 1 << 24;
            const RWP = 1 << 3;
            const IR = 1 << 2;
            const CES = 1 << 1;
            const EnableLPIs = 1 << 0;
        }

        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        pub struct GicrWaker: u32 {
            const ChildrenAsleep = 1 << 2;
            const ProcessorSleep = 1 << 1;
        }
    }

    // TargetListFilter
    pub const GIDG_SGIR_TARGET_LIST: u32 = 0b00;
    pub const GIDG_SGIR_TARGET_ALL_EXCEPT_SELF: u32 = 0b01 << 24;
    pub const _GIDG_SGIR_TARGET_SELF: u32 = 0b10 << 24;

    // GICD_base
    mmio_rw!(offset 0x0000 => pub GICD_CTLR<GicdCtlr>);
    mmio_rw!(offset 0x0004 => pub GICD_TYPER<u32>);
    mmio_rw!(offset 0x0080 => pub GICD_IGROUPR<u32>);
    mmio_rw!(offset 0x0100 => pub GICD_ISENABLER<u32>);
    mmio_rw!(offset 0x0180 => pub GICD_ICENABLER<u32>);
    mmio_rw!(offset 0x0280 => pub GICD_ICPENDR<u32>);
    mmio_rw!(offset 0x0380 => pub GICD_ICACTIVER<u32>);
    mmio_rw!(offset 0x0400 => pub GICD_IPRIORITYR<u32>);
    mmio_rw!(offset 0x0800 => pub GICD_ITARGETSR<u32>);
    mmio_rw!(offset 0x0c00 => pub GICD_ICFGR<u32>);
    mmio_w! (offset 0x0F00 => pub GICD_SGIR<u32>);
    mmio_rw!(offset 0x6000 => pub GICD_IROUTER<u32>);

    // GICR_base
    mmio_rw!(offset 0x0000 => pub GICR_CTLR<GicrCtlr>);
    mmio_rw!(offset 0x0008 => pub GICR_TYPER<u32>);
    mmio_rw!(offset 0x0014 => pub GICR_WAKER<GicrWaker>);

    // SGI_base
    mmio_rw!(offset 0x0080 => pub GICR_IGROUPR0<u32>);
    mmio_rw!(offset 0x0100 => pub GICR_ISENABLER0<u32>);
    mmio_rw!(offset 0x0400 => pub GICR_IPRIORITYR<u32>);
    mmio_rw!(offset 0x0C00 => pub GICR_ICFGR0<u32>);
    mmio_rw!(offset 0x0C04 => pub GICR_ICFGR1<u32>);
}

#[derive(Default)]
pub struct GICv3 {
    gicd_base: usize,
    gicr_base: usize,
    sgi_base: usize,
}

const SGI_OFFSET: usize = 0x10000;

impl GICv3 {
    pub fn new(gicd_base: usize, gicr_base: usize) -> Self {
        // Enable system register access.
        unsafe { awkernel_aarch64::icc_sre_el1::set(1) };

        let gicd_ctlr = registers::GICD_CTLR.read(gicd_base);
        if gicd_ctlr.contains(registers::GicdCtlr::DS) {
            log::info!("GICv3 is non secure mode.");
            Self::new_non_secure(gicd_base, gicr_base)
        } else {
            log::info!("GICv3 is secure mode.");
            unimplemented!();
        }
    }

    fn new_non_secure(gicd_base: usize, gicr_base: usize) -> Self {
        let sgi_base = gicr_base + SGI_OFFSET;
        let gic = GICv3 {
            gicd_base,
            gicr_base,
            sgi_base,
        };

        // Disable group 0 and 1.
        registers::GICD_CTLR.clrbits(
            registers::GicdCtlr::EnableGrp0 | registers::GicdCtlr::EnableGrp1NS,
            gicd_base,
        );

        // Dsable LPIs.
        registers::GICR_CTLR.write(registers::GicrCtlr::empty(), gicr_base);

        // Enable affinity routing.
        registers::GICD_CTLR.setbits(registers::GicdCtlr::ARE_S, gicd_base);

        Self::wake_children(gicr_base);
        Self::set_priority_mask();
        Self::set_eoi_mode_zero();
        Self::enable_igrp();

        // ITLinesNumber, bits [4:0]
        let it_lines_number = registers::GICD_TYPER.read(gicd_base) & 0x1f;

        // The number of implemented GICD_IPRIORITYRs is (8 * (GICD_TYPER.ITLinesNumber+1)).
        for i in 0..(8 * (it_lines_number + 1)) {
            let base = gicd_base + (i * 4) as usize;
            registers::GICD_IPRIORITYR.write(0xa0a0a0a0, base);
        }

        // GICR_IPRIORITYR0-GICR_IPRIORITYR3 store the priority of SGIs.
        // GICR_IPRIORITYR4-GICR_IPRIORITYR7 store the priority of PPIs.
        for i in 0..8 {
            let base = sgi_base + i * 4;
            registers::GICR_IPRIORITYR.write(0xa0a0a0a0, base);
        }

        // The number of implemented GICD_IGROUPR registers is (GICD_TYPER.ITLinesNumber + 1)
        for i in 0..(it_lines_number + 1) {
            let base = gicd_base + (i * 4) as usize;
            registers::GICD_IGROUPR.write(!0, base); // Group 1.
        }

        registers::GICR_IGROUPR0.write(!0, sgi_base); // Group 1.

        // Config all interrupts to level triggered.
        // For SGIs, Int_config fields are RO, meaning that GICD_ICFGR0 is RO.

        let processor_number = (registers::GICR_TYPER.read(gicr_base) >> 8) & 0xffff;

        // GICD_ICFGR1 is Banked for each connected PE with GICR_TYPER.Processor_Number < 8.
        // Accessing GICD_ICFGR1 from a PE with GICR_TYPER.Processor_Number > 7 is CONSTRAINED UNPREDICTABLE:
        if processor_number < 8 {
            // Corresponding interrupt is level-sensitive.
            registers::GICD_ICFGR.write(0, gicr_base + 4);
        }

        for i in 2..64 {
            let base = gicd_base + i * 4;
            // Corresponding interrupt is level-sensitive.
            registers::GICD_ICFGR.write(0, base);
        }

        registers::GICR_ICFGR0.write(0, sgi_base);
        registers::GICR_ICFGR1.write(0, sgi_base);

        // The maximum value of n is given by (32*(GICD_TYPER.ITLinesNumber+1) - 1).
        for n in 0..(32 * (it_lines_number + 1)) {
            let base = gicd_base + (n * 4) as usize;
            // Interrupts routed to the PE specified by a.b.c.d. In this routing, a, b, c,
            // and d are the values of fields Aff3, Aff2, Aff1, and Aff0 respectively.
            // All SPIs will be delivered to the CPU #0.
            registers::GICD_IROUTER.write(1 << 31, base); // Interrupt_Routing_Mode, bit [31]
        }

        // Enable the distributor.
        registers::GICD_CTLR.setbits(
            registers::GicdCtlr::EnableGrp0 | registers::GicdCtlr::EnableGrp1NS,
            gicd_base,
        );

        // Enable LPIs.
        registers::GICR_CTLR.write(registers::GicrCtlr::EnableLPIs, gicr_base);

        gic
    }

    /// On reset, a Redistributor treats the PE to which it is connected as sleeping.
    /// Wake-up is controlled through GICR_WAKER. To mark the connected PE as being awake, software must:
    /// - Clear GICR_WAKER.ProcessorSleep to 0.
    /// - Poll GICR_WAKER.ChildrenAsleep until it reads 0.
    fn wake_children(gicr_base: usize) {
        registers::GICR_WAKER.clrbits(registers::GicrWaker::ProcessorSleep, gicr_base);
        while registers::GICR_WAKER
            .read(gicr_base)
            .contains(registers::GicrWaker::ProcessorSleep)
        {}
    }

    /// The Priority Mask sets the minimum priority an interrupt must have in order to be forwarded to the PE.
    /// EOImode (0): ICC_EOIR0 and ICC_EOIR1 provide both priority drop and interrupt deactivation functionality
    fn set_eoi_mode_zero() {
        let eoi_mode = 1 << 1;
        let icc_ctlr = awkernel_aarch64::icc_ctlr_el1::get();
        unsafe { awkernel_aarch64::icc_ctlr_el1::set(icc_ctlr & !eoi_mode) };
    }

    /// Enable signaling of each interrupt group.
    fn enable_igrp() {
        unsafe {
            awkernel_aarch64::icc_igrpen0_el1::set(1);
            awkernel_aarch64::icc_igrpen1_el1::set(1);
        }
    }

    fn set_priority_mask() {
        unsafe { awkernel_aarch64::icc_pmr_el1::set(0xf0) };
    }
}

impl InterruptController for GICv3 {
    fn enable_irq(&mut self, irq: u16) {
        if irq < 1020 {
            let idx = irq >> 5;
            let mask = 1 << (irq & (NUM_INTS_PER_REG - 1)) as u32;
            let base = self.gicd_base + idx as usize * 4;

            registers::GICD_ISENABLER.write(mask, base);
            if irq < 32 {
                registers::GICR_ISENABLER0.write(mask, self.sgi_base);
            }

            let cpu_id = awkernel_lib::cpu::cpu_id();
            log::info!("GICv3: IRQ #{irq} has been enabled on CPU#{cpu_id}.");
        } else {
            log::warn!("GICv3: IRQ #{irq} is not supported.");
        }
    }

    fn disable_irq(&mut self, irq: u16) {
        if irq < 1020 {
            let idx = irq >> 5;
            let mask = 1 << (irq & (NUM_INTS_PER_REG - 1)) as u32;
            let base = self.gicd_base + idx as usize * 4;

            registers::GICD_ICENABLER.write(mask, base);
            if irq < 32 {
                // registers::GICR_ICENABLER0.write(mask, self.sgi_base);
            }

            let cpu_id = awkernel_lib::cpu::cpu_id();
            log::info!("GICv3: IRQ #{irq} has been disabled on CPU#{cpu_id}.");
        } else {
            log::warn!("GICv3: IRQ #{irq} is not supported.");
        }
    }

    fn init_non_primary(&mut self) {}

    fn send_ipi(&mut self, irq: u16, target: u16) {}

    fn send_ipi_broadcast(&mut self, irq: u16) {}

    fn send_ipi_broadcast_without_self(&mut self, irq: u16) {}

    fn pending_irqs<'a>(&self) -> Box<dyn Iterator<Item = u16>> {
        todo!()
    }
}
