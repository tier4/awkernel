//! | INTID            | Interrupt Type           | Notes                                        |
//! |------------------|--------------------------|----------------------------------------------|
//! | 0-15             | SGIs                     | Banked per PE                                |
//! | 16-31            | PPIs                     | Banked per PE                                |
//! | 32 - 1019        | SPIs                     |                                              |
//! | 1020 - 1023      | Special interrupt number | Used to signal special cases                 |
//! | 1024 - 8191      | Reserved LPIs            |                                              |
//! | 8192 and greater | LPIs                     | The upper boundary is IMPLEMENTATION DEFINED |

use alloc::boxed::Box;
use awkernel_lib::interrupt::InterruptController;

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

    mmio_rw!(offset 0x000 => pub GICD_CTLR<GicdCtlr>);
    mmio_rw!(offset 0x080 => pub GICD_IGROUPR<u32>);
    mmio_rw!(offset 0x100 => pub GICD_ISENABLER<u32>);
    mmio_rw!(offset 0x180 => pub GICD_ICENABLER<u32>);
    mmio_rw!(offset 0x280 => pub GICD_ICPENDR<u32>);
    mmio_rw!(offset 0x380 => pub GICD_ICACTIVER<u32>);
    mmio_rw!(offset 0x400 => pub GICD_IPRIORITYR<u32>);
    mmio_rw!(offset 0x800 => pub GICD_ITARGETSR<u32>);
    mmio_rw!(offset 0xc00 => pub GICD_ICFGR<u32>);
    mmio_w! (offset 0xF00 => pub GICD_SGIR<u32>);

    mmio_rw!(offset 0x000 => pub GICR_CTLR<GicrCtlr>);
    mmio_rw!(offset 0x014 => pub GICR_WAKER<GicrWaker>);
}

#[derive(Default)]
pub struct GICv3 {
    gicd_base: usize,
    gicr_base: usize,
}

impl GICv3 {
    pub fn new(gicd_base: usize, gicr_base: usize) -> Self {
        // Disable Group 0 and 1.
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
        let gic = GICv3 {
            gicd_base,
            gicr_base,
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
        Self::set_eoi_mode_zero();

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
}

impl InterruptController for GICv3 {
    fn enable_irq(&mut self, irq: u16) {}

    fn disable_irq(&mut self, irq: u16) {}

    fn init_non_primary(&mut self) {}

    fn send_ipi(&mut self, irq: u16, target: u16) {}

    fn send_ipi_broadcast(&mut self, irq: u16) {}

    fn send_ipi_broadcast_without_self(&mut self, irq: u16) {}

    fn pending_irqs<'a>(&self) -> Box<dyn Iterator<Item = u16>> {
        todo!()
    }
}
