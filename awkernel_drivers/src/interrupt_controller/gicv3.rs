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
//!
//! # References
//!
//! - <https://github.com/NetBSD/src/blob/netbsd-9/sys/arch/arm/cortex/gicv3.c>
//! - <https://github.com/NetBSD/src/blob/netbsd-9/sys/arch/arm/cortex/gicv3_its.c>
//! - <https://www.kernel.org/doc/Documentation/devicetree/bindings/interrupt-controller/arm%2Cgic-v3.txt>

use alloc::{boxed::Box, collections::BTreeMap};
use awkernel_lib::{
    addr::{virt_addr::VirtAddr, Addr},
    arch::aarch64::{current_affinity, get_affinity},
    cpu::NUM_MAX_CPU,
    dma_pool::DMAPool,
    interrupt::InterruptController,
    paging::PAGESIZE,
};
use core::hint::spin_loop;

const NUM_INTS_PER_REG: u16 = 32;

mod registers {
    use awkernel_lib::mmio_rw;
    use bitflags::bitflags;

    bitflags! {
        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        pub struct GicdCtlrSecure: u32 {
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
        pub struct GicdCtlrNonSecure: u32 {
            const RWP = 1 << 31;
            const ARE_NS = 1 << 4;
            const EnableGrp1 = 1 << 1;
            const EnableGrp0 = 1 << 0;
        }

        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        pub struct GicdCtlr: u32 {
            /// RWP is 1 during the following fields are updating.
            /// - GICD_CTLR[2:0], the Group Enables, for transitions from 1 to 0 only.
            /// - GICD_CTLR[7:4], the ARE bits, E1NWF bit and DS bit.
            /// - GICD_ICENABLER<n>.
            const RWP = 1 << 31;

            const nASSGIreq = 1 << 8;
            const E1NWF = 1 << 7;
            const DS = 1 << 6;
            const ARE = 1 << 4;
            const EnableGrp1 = 1 << 1;
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

    pub const _GICD_TYPER_LPIS: u32 = 1 << 17;

    // GICD_base
    mmio_rw!(offset 0x0000 => pub GICD_CTLR<GicdCtlr>); // Single security mode.
    mmio_rw!(offset 0x0000 => pub GICD_CTLR_SECURE<GicdCtlrSecure>); // Secure mode.
    mmio_rw!(offset 0x0000 => pub GICD_CTLR_NON_SECURE<GicdCtlrNonSecure>); // Non-secure mode.
    mmio_rw!(offset 0x0004 => pub GICD_TYPER<u32>);
    mmio_rw!(offset 0x0080 => pub GICD_IGROUPR<u32>);
    mmio_rw!(offset 0x0100 => pub GICD_ISENABLER<u32>);
    mmio_rw!(offset 0x0180 => pub GICD_ICENABLER<u32>);
    mmio_rw!(offset 0x0280 => pub GICD_ICPENDR<u32>);
    mmio_rw!(offset 0x0400 => pub GICD_IPRIORITYR<u32>);
    mmio_rw!(offset 0x0c00 => pub GICD_ICFGR<u32>);
    mmio_rw!(offset 0x0D00 => pub GICD_IGRPMODR<u32>);
    mmio_rw!(offset 0x6000 => pub GICD_IROUTER<u64>);

    // GICR_base
    mmio_rw!(offset 0x0000 => pub GICR_CTLR<GicrCtlr>);
    mmio_rw!(offset 0x0008 => pub GICR_TYPER<u64>);
    mmio_rw!(offset 0x0014 => pub GICR_WAKER<GicrWaker>);
    mmio_rw!(offset 0x0070 => pub GICR_PROPBASER<u64>);
    mmio_rw!(offset 0x0078 => pub GICR_PENDBASER<u64>);

    // SGI_base
    mmio_rw!(offset 0x0080 => pub GICR_IGROUPR0<u32>);
    mmio_rw!(offset 0x0100 => pub GICR_ISENABLER0<u32>);
    mmio_rw!(offset 0x0180 => pub GICR_ICENABLER0<u32>);
    mmio_rw!(offset 0x0280 => pub GICR_ICPENDR0<u32>);
    mmio_rw!(offset 0x0400 => pub GICR_IPRIORITYR<u32>);
    mmio_rw!(offset 0x0C00 => pub GICR_ICFGR0<u32>);
    mmio_rw!(offset 0x0C04 => pub GICR_ICFGR1<u32>);
}

const LPI_CFG_TABLE_SZ: usize = 65536;
const LPI_PEND_TABLE_SZ: usize = 65536 / 8;

#[allow(dead_code)] // TODO: remove this attribute
pub struct GICv3 {
    gicd_base: usize,
    gicr_base: usize,
    its_base: Option<usize>,
    cpu_gicr: BTreeMap<u64, usize>,
    lpi_cfg_table: Option<CachedPool<LPI_CFG_TABLE_SZ>>,
    lpi_pend_table: Option<CachedPool<LPI_PEND_TABLE_SZ>>,
}

const SGI_OFFSET: usize = 0x10000;

fn wait_gicd_rwp(gicd_base: usize) {
    while registers::GICD_CTLR
        .read(gicd_base)
        .contains(registers::GicdCtlr::RWP)
    {
        spin_loop();
    }
}

fn wait_gicr_rwp(gicr_base: usize) {
    while registers::GICR_CTLR
        .read(gicr_base)
        .contains(registers::GicrCtlr::RWP)
    {
        spin_loop();
    }
}

fn cpu_identity() -> u64 {
    let (aff3, aff2, aff1, aff0) = current_affinity();
    (aff3 as u64) << 56 | (aff2 as u64) << 48 | (aff1 as u64) << 40 | (aff0 as u64) << 32
}

impl GICv3 {
    pub fn new(gicd_base: usize, gicr_base: usize, its_base: Option<usize>) -> Self {
        let gicd_ctlr = registers::GICD_CTLR.read(gicd_base);
        if gicd_ctlr.contains(registers::GicdCtlr::DS) {
            log::info!("GICv3 is non secure mode.");
            Self::new_non_secure(gicd_base, gicr_base, its_base)
        } else {
            log::info!("GICv3 is secure mode.");
            unimplemented!();
        }
    }

    fn new_non_secure(gicd_base: usize, gicr_base: usize, its_base: Option<usize>) -> Self {
        let typer = registers::GICD_TYPER.read(gicd_base);

        // ITLinesNumber, bits [4:0]
        let it_lines_number = typer & 0x1f;
        let gic_max_int = it_lines_number * 32;

        // Disable GICD.
        registers::GICD_CTLR.write(registers::GicdCtlr::empty(), gicd_base);
        wait_gicd_rwp(gicd_base);

        // Clear SPIs, set group 1.
        for i in (1..gic_max_int).step_by(32) {
            let base = gicd_base + i as usize / 8;
            registers::GICD_ICENABLER.write(!0, base);
            registers::GICD_ICPENDR.write(!0, base);
            registers::GICD_IGROUPR.write(!0, base);
            registers::GICD_IGRPMODR.write(0, base);
        }
        wait_gicd_rwp(gicd_base);

        // The number of implemented GICD_IPRIORITYRs is (8 * (GICD_TYPER.ITLinesNumber+1)).
        for i in 0..(8 * (it_lines_number + 1)) {
            let base = gicd_base + (i * 4) as usize;
            registers::GICD_IPRIORITYR.write(0xa0a0a0a0, base);
        }

        // Config all interrupts to level triggered.
        // For SGIs, Int_config fields are RO, meaning that GICD_ICFGR0 is RO.

        let processor_number = (registers::GICR_TYPER.read(gicr_base) >> 8) & 0xffff;

        // GICD_ICFGR1 is Banked for each connected PE with GICR_TYPER.Processor_Number < 8.
        // Accessing GICD_ICFGR1 from a PE with GICR_TYPER.Processor_Number > 7 is CONSTRAINED UNPREDICTABLE:
        if processor_number < 8 {
            // Corresponding interrupt is level-sensitive.
            registers::GICD_ICFGR.write(0, gicd_base + 4);
        }

        // The maximum value of n is given by (32*(GICD_TYPER.ITLinesNumber+1) - 1).
        for n in 0..(32 * (it_lines_number + 1)) {
            let base = gicd_base + (n * 8) as usize;
            // Interrupts routed to the PE specified by a.b.c.d. In this routing, a, b, c,
            // and d are the values of fields Aff3, Aff2, Aff1, and Aff0 respectively.
            // All SPIs will be delivered to the CPU #0.
            registers::GICD_IROUTER.write(0, base); // Interrupt_Routing_Mode, bit [31]
        }

        // Enable group 1 and affinity routing.
        registers::GICD_CTLR.write(
            registers::GicdCtlr::EnableGrp1 | registers::GicdCtlr::ARE | registers::GicdCtlr::E1NWF,
            gicd_base,
        );
        wait_gicd_rwp(gicd_base);

        let (lpi_cfg_table, lpi_pend_table) = if its_base.is_some() {
            (
                Some(unsafe { init_lpi_cfg_table(gicr_base).unwrap() }),
                Some(unsafe { init_lpi_pend_table(gicr_base).unwrap() }),
            )
        } else {
            (None, None)
        };

        let mut gic = GICv3 {
            gicd_base,
            gicr_base,
            its_base,
            cpu_gicr: BTreeMap::new(),
            lpi_cfg_table,
            lpi_pend_table,
        };

        gic.init_per_cpu();

        gic
    }

    fn find_redist(&mut self) -> Option<usize> {
        let cpu_id = cpu_identity() >> 32;

        for i in 0..NUM_MAX_CPU {
            let base = self.gicr_base + i * 0x20000;
            let typer = registers::GICR_TYPER.read(base);
            if cpu_id == typer >> 32 {
                self.cpu_gicr.insert(cpu_id, base);
                return Some(base);
            }
        }

        None
    }

    fn init_per_cpu(&mut self) {
        let Some(gicr_base) = self.find_redist() else {
            log::error!("could not find GICR_BASE");
            return;
        };

        let sgi_base = gicr_base + SGI_OFFSET;

        Self::wake_children(gicr_base);

        registers::GICR_IGROUPR0.write(!0, sgi_base);
        wait_gicr_rwp(gicr_base);

        registers::GICR_ICENABLER0.write(!0, sgi_base);
        registers::GICR_ICPENDR0.write(!0, sgi_base);
        wait_gicr_rwp(gicr_base);

        // Enable system register access.
        let sre = awkernel_aarch64::icc_sre_el1::get();
        if sre & 1 == 0 {
            unsafe { awkernel_aarch64::icc_sre_el1::set(sre & 1) };
        }

        registers::GICR_ISENABLER0.write(!0, sgi_base);
        wait_gicr_rwp(gicr_base);

        Self::init_eoi_mode_zero();
        Self::init_priority_mask();
        Self::enable_igrp();
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
    fn init_eoi_mode_zero() {
        let eoi_mode = 1 << 1;
        let icc_ctlr = awkernel_aarch64::icc_ctlr_el1::get();
        unsafe { awkernel_aarch64::icc_ctlr_el1::set(icc_ctlr & !eoi_mode) };
    }

    /// Enable signaling of the interrupt group 1.
    fn enable_igrp() {
        unsafe { awkernel_aarch64::icc_igrpen1_el1::set(1) };
    }

    fn init_priority_mask() {
        unsafe { awkernel_aarch64::icc_pmr_el1::set(0xf0) };
    }
}

impl InterruptController for GICv3 {
    fn enable_irq(&mut self, irq: u16) {
        if irq < 1020 {
            let idx = irq >> 5;
            let mask = 1 << (irq & (NUM_INTS_PER_REG - 1)) as u32;
            let base = self.gicd_base + idx as usize * 4;

            if irq < 32 {
                let id = cpu_identity();
                if let Some(gicr_base) = self.cpu_gicr.get(&id) {
                    let sgi_base = gicr_base + SGI_OFFSET;
                    registers::GICR_ISENABLER0.write(mask, sgi_base);
                    wait_gicr_rwp(*gicr_base);
                }
            } else {
                registers::GICD_ISENABLER.write(mask, base);
                wait_gicd_rwp(self.gicd_base);
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

            if irq < 32 {
                let id = cpu_identity();
                if let Some(gicr_base) = self.cpu_gicr.get(&id) {
                    let sgi_base = gicr_base + SGI_OFFSET;
                    registers::GICR_ICENABLER0.write(mask, sgi_base);
                    wait_gicr_rwp(*gicr_base);
                }
            } else {
                registers::GICD_ICENABLER.write(mask, base);
                wait_gicd_rwp(self.gicd_base);
            }

            let cpu_id = awkernel_lib::cpu::cpu_id();
            log::info!("GICv3: IRQ #{irq} has been disabled on CPU#{cpu_id}.");
        } else {
            log::warn!("GICv3: IRQ #{irq} is not supported.");
        }
    }

    fn init_non_primary(&mut self) {
        self.init_per_cpu();
    }

    fn send_ipi(&mut self, irq: u16, cpu_id: u32) {
        const ICC_CTLR_RSS: u64 = 1 << 18;
        const GICD_TYPER_RSS: u32 = 1 << 26;

        let Some((aff0, aff1, aff2, aff3)) = get_affinity(cpu_id as usize) else {
            return;
        };

        let (rs, target_list) = if (awkernel_aarch64::icc_ctlr_el1::get() & ICC_CTLR_RSS) != 0
            && registers::GICD_TYPER.read(self.gicd_base) & GICD_TYPER_RSS != 0
        {
            // Targeted SGIs with affinity level 0 values of 0 - 255 are supported.
            ((aff0 as u64 & 0xf0) << 40, (1 << (aff0 & 0x0f)) as u64)
        } else {
            // Targeted SGIs with affinity level 0 values of 0 - 15 are supported.
            (0, 1 << (aff0 & 0x0f))
        };

        let reg = (aff3 as u64) << 48
            | rs
            | (aff2 as u64) << 32
            | (irq as u64 & 0x0f) << 24
            | (aff1 as u64) << 16
            | target_list;

        unsafe { awkernel_aarch64::icc_sgi1r_el1::set(reg) }
    }

    fn send_ipi_broadcast(&mut self, irq: u16) {
        self.send_ipi_broadcast_without_self(irq);
        let id = awkernel_lib::cpu::cpu_id();
        self.send_ipi(irq, id as u32);
    }

    fn send_ipi_broadcast_without_self(&mut self, irq: u16) {
        const ICC_SGI1R_EL1_IRM: u64 = 1 << 40;
        unsafe {
            awkernel_aarch64::icc_sgi1r_el1::set(ICC_SGI1R_EL1_IRM | ((irq as u64) & 0x0f) << 24)
        }
    }

    fn pending_irqs<'a>(&self) -> Box<dyn Iterator<Item = u16>> {
        Box::new(PendingInterruptIterator)
    }

    fn irq_range(&self) -> (u16, u16) {
        // IRQ #0: preemption
        // IRQ #1: wakeup CPUs
        (2, 1024)
    }

    fn irq_range_for_pnp(&self) -> (u16, u16) {
        (96, 1020)
    }

    fn set_pcie_msi(
        &self,
        _segment_number: usize,
        _target: u32,
        _irq: u16,
        _message_data: &mut u32,
        _message_address: &mut u32,
        _message_address_upper: Option<&mut u32>,
    ) -> Result<awkernel_lib::interrupt::IRQ, &'static str> {
        Err("GICv3: set_pcie_msi is not yet implemented.")
    }
}

pub struct PendingInterruptIterator;

const ID_SPURIOUS: u16 = 1023;

impl Iterator for PendingInterruptIterator {
    type Item = u16;

    fn next(&mut self) -> Option<Self::Item> {
        let id = awkernel_aarch64::icc_iar1_el1::get() as u16;

        if id == ID_SPURIOUS {
            None
        } else {
            unsafe { awkernel_aarch64::icc_eoir1_el1::set(id as u64) };
            Some(id)
        }
    }
}

const NORMAL_INNER_CACHEABLE_READ_ALLOCATE_WRITE_ALLOCATE_WRITE_BACK: u64 = 0b11 << 7;
const INNER_SHAREABLE: u64 = 0b01 << 10;

/// A cached DMA pool.
struct CachedPool<const N: usize> {
    pool: DMAPool<[u8; N]>,
}

impl<const N: usize> CachedPool<N> {
    fn new() -> Result<Self, &'static str> {
        let mut pool =
            DMAPool::<[u8; N]>::new(0, N / PAGESIZE).ok_or("failed to create dma pool")?;

        let virt_addr = pool.get_virt_addr();
        for i in 0..pool.get_size() / PAGESIZE {
            let virt_addr = virt_addr + i * PAGESIZE;
            unsafe { enable_cache(virt_addr)? };
        }

        for n in pool.as_mut().iter_mut() {
            *n = 0;
        }

        Ok(Self { pool })
    }
}

impl<const N: usize> Drop for CachedPool<N> {
    fn drop(&mut self) {
        let virt_addr = self.pool.get_virt_addr();
        for i in 0..self.pool.get_size() / PAGESIZE {
            let virt_addr = virt_addr + i * PAGESIZE;
            unsafe { disable_cache(virt_addr).unwrap() };
        }
    }
}

/// Initialize the LPI Configuration Table.
/// Because a continuous block of memory is required for the LPI Configuration Table,
/// the LPI Configuration Table is created as a DMA pool.
/// To improve performance, the DMA pool is mapped with the cache enabled.
///
/// # Safety
///
/// The `gicr_base` must be a valid address.
unsafe fn init_lpi_cfg_table(
    gicr_base: usize,
) -> Result<CachedPool<LPI_CFG_TABLE_SZ>, &'static str> {
    let pool = CachedPool::<LPI_CFG_TABLE_SZ>::new()?;

    registers::GICR_PROPBASER.write(
        pool.pool.get_phy_addr().as_usize() as u64
            | INNER_SHAREABLE
            | NORMAL_INNER_CACHEABLE_READ_ALLOCATE_WRITE_ALLOCATE_WRITE_BACK
            | 15,
        gicr_base,
    );

    Ok(pool)
}

/// Initialize the LPI Pending Table.
/// Because a continuous block of memory is required for the LPI Pending Table,
/// the LPI Pending Table is created as a DMA pool.
/// To improve performance, the DMA pool is mapped with the cache enabled.
///
/// # Safety
///
/// The `gicr_base` must be a valid address.
unsafe fn init_lpi_pend_table(
    gicr_base: usize,
) -> Result<CachedPool<LPI_PEND_TABLE_SZ>, &'static str> {
    let pool = CachedPool::<LPI_PEND_TABLE_SZ>::new()?;

    registers::GICR_PENDBASER.write(
        pool.pool.get_phy_addr().as_usize() as u64
            | INNER_SHAREABLE
            | NORMAL_INNER_CACHEABLE_READ_ALLOCATE_WRITE_ALLOCATE_WRITE_BACK,
        gicr_base,
    );

    Ok(pool)
}

/// Make the memory region specified by `virt_addr` cacheable.
///
/// # Safety
///
/// The `virt_addr` must be a valid address.
unsafe fn enable_cache(virt_addr: VirtAddr) -> Result<(), &'static str> {
    let phy_addr =
        awkernel_lib::paging::vm_to_phy(virt_addr).ok_or("failed to translate VM to Phy")?;

    awkernel_lib::paging::unmap(virt_addr);

    if let Err(e) = awkernel_lib::paging::map(
        virt_addr,
        phy_addr,
        awkernel_lib::paging::Flags {
            execute: false,
            write: true,
            cache: true,
            device: false,
            write_through: false,
        },
    ) {
        log::error!("failed to map: {e:?}, virt_addr: {virt_addr:?}");
        return Err("failed to map");
    }

    Ok(())
}

/// Disable the cache for the memory region specified by `virt_addr`.
///
/// # Safety
///
/// The `virt_addr` must be a valid address.
unsafe fn disable_cache(virt_addr: VirtAddr) -> Result<(), &'static str> {
    let phy_addr =
        awkernel_lib::paging::vm_to_phy(virt_addr).ok_or("failed to translate VM to Phy")?;

    awkernel_lib::paging::unmap(virt_addr);

    if let Err(e) = awkernel_lib::paging::map(
        virt_addr,
        phy_addr,
        awkernel_lib::paging::Flags {
            execute: false,
            write: true,
            cache: false,
            device: true,
            write_through: false,
        },
    ) {
        log::error!("failed to map: {e:?}, virt_addr: {virt_addr:?}");
        return Err("failed to map");
    }

    Ok(())
}
