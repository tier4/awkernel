//! xHCI host controller driver: controller bring-up (reset, rings, start).
//!
//! The driver is fully polled (USBCMD.INTE = 0).
//!
//! Path classification:
//! - Non-RT: [`attach`] and everything it calls (controller reset and start).
//!   Runs once at boot; allocates DMA pages and busy-waits with bounded polling
//!   budgets.

use alloc::{borrow::Cow, format, string::String, sync::Arc, vec::Vec};
use core::cell::UnsafeCell;

use awkernel_lib::{addr::Addr, dma_pool::DMAPool};

use super::super::{
    mmio::{Mmio, MmioErr},
    registers::StatusCommand,
    PCIeDevice, PCIeDeviceErr, PCIeInfo,
};

mod regs;
mod ring;

use regs::{completion, trb_type};
use ring::{publish, CommandRing, Dcbaa, EventRing, Trb};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Polling budget for controller state transitions (USBSTS / USBCMD / PORTSC).
const STATE_POLL_ITERS: u32 = 1_000_000;
/// Polling budget for one command or transfer completion event.
const COMPLETION_POLL_ITERS: u32 = 2_000_000;

/// All DMA allocations go to NUMA node 0.
const NUMA_NODE: usize = 0;
const PAGE_SIZE: usize = 4096;
type Page = [u8; PAGE_SIZE];

/// Scratchpad pointer array: one 8-byte entry per page, in one DMA page.
const MAX_SCRATCHPAD: usize = PAGE_SIZE / 8;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum XhciErr {
    /// BAR[0] is not MMIO, or a register offset fell outside it.
    Mmio,
    DmaAlloc,
    Overflow,
    /// A command or transfer did not complete within its polling budget.
    Timeout,
    /// A command or transfer completed with this (non-success) completion code.
    Completion(u8),
    RingFull,
}

impl From<XhciErr> for PCIeDeviceErr {
    fn from(e: XhciErr) -> Self {
        log::error!("xHCI: {e:?}");
        match e {
            XhciErr::Mmio => PCIeDeviceErr::BARFailure,
            XhciErr::Timeout | XhciErr::Completion(_) => PCIeDeviceErr::CommandFailure,
            _ => PCIeDeviceErr::InitFailure,
        }
    }
}

impl From<MmioErr> for XhciErr {
    fn from(e: MmioErr) -> Self {
        match e {
            MmioErr::NotMmio | MmioErr::OutOfRange => XhciErr::Mmio,
            MmioErr::Overflow => XhciErr::Overflow,
            MmioErr::Timeout => XhciErr::Timeout,
        }
    }
}

fn phys_of<T>(pool: &DMAPool<T>) -> Result<u64, XhciErr> {
    u64::try_from(pool.get_phy_addr().as_usize()).map_err(|_| XhciErr::Overflow)
}

fn lo32(v: u64) -> u32 {
    let [a, b, c, d, ..] = v.to_le_bytes();
    u32::from_le_bytes([a, b, c, d])
}

fn hi32(v: u64) -> u32 {
    let [.., a, b, c, d] = v.to_le_bytes();
    u32::from_le_bytes([a, b, c, d])
}

fn new_page() -> Result<DMAPool<Page>, XhciErr> {
    let mut page = DMAPool::<Page>::new(NUMA_NODE, 1).ok_or(XhciErr::DmaAlloc)?;
    page.as_mut().fill(0);
    Ok(page)
}

// ---------------------------------------------------------------------------
// Controller core: command ring, event ring and doorbells
// ---------------------------------------------------------------------------

struct HcCore {
    op: Mmio,
    ir0: Mmio,
    db: Mmio,
    cmd_ring: CommandRing,
    evt_ring: EventRing,
}

impl HcCore {
    fn ring_doorbell(&self, slot: u8, target: u8) -> Result<(), XhciErr> {
        let off = usize::from(slot).checked_mul(4).ok_or(XhciErr::Overflow)?;
        publish();
        Ok(self.db.write32(off, u32::from(target))?)
    }

    /// Tell the controller how far the event ring has been consumed.
    fn update_erdp(&self) -> Result<(), XhciErr> {
        let erdp = self.evt_ring.dequeue_phys()?;
        self.ir0
            .write32(regs::ir::ERDP_LO, lo32(erdp) | regs::ir::ERDP_EHB)?;
        Ok(self.ir0.write32(regs::ir::ERDP_HI, hi32(erdp))?)
    }

    /// Wait for the next event of type `kind`, discarding other events.
    ///
    /// WCET: at most `COMPLETION_POLL_ITERS` event-ring polls.
    fn wait_event(&mut self, kind: u32) -> Result<Trb, XhciErr> {
        for _ in 0..COMPLETION_POLL_ITERS {
            if let Some(trb) = self.evt_ring.dequeue()? {
                self.update_erdp()?;
                if trb.trb_type() == kind {
                    return Ok(trb);
                }
            }
            core::hint::spin_loop();
        }
        Err(XhciErr::Timeout)
    }

    /// Submit a command and wait for its Command Completion event.
    fn command(&mut self, trb: Trb) -> Result<Trb, XhciErr> {
        self.cmd_ring.enqueue(trb)?;
        self.ring_doorbell(0, 0)?;
        let event = self.wait_event(trb_type::CMD_COMPLETION)?;
        match event.completion_code() {
            completion::SUCCESS => Ok(event),
            code => Err(XhciErr::Completion(code)),
        }
    }
}

// ---------------------------------------------------------------------------
// Controller
// ---------------------------------------------------------------------------

struct Controller {
    name: String,
    core: HcCore,
    dcbaa: Dcbaa,
    max_slots: u8,
    max_scratchpad: usize,
    /// Scratchpad pointer array and pages; owned by the controller for its lifetime.
    _scratchpad: Vec<DMAPool<Page>>,
}

impl Controller {
    fn new(cap: Mmio, name: String) -> Result<Self, XhciErr> {
        let caplength = usize::from(cap.read8(regs::cap::CAPLENGTH)?);
        let hci_version = cap.read16(regs::cap::HCIVERSION)?;
        let hcsparams1 = cap.read32(regs::cap::HCSPARAMS1)?;
        let hcsparams2 = cap.read32(regs::cap::HCSPARAMS2)?;
        let hccparams1 = cap.read32(regs::cap::HCCPARAMS1)?;
        let dboff =
            usize::try_from(cap.read32(regs::cap::DBOFF)?).map_err(|_| XhciErr::Overflow)?;
        let rtsoff =
            usize::try_from(cap.read32(regs::cap::RTSOFF)?).map_err(|_| XhciErr::Overflow)?;

        // HCSPARAMS1: MaxSlots[7:0], MaxIntrs[18:8], MaxPorts[31:24].
        let [max_slots, ..] = hcsparams1.to_le_bytes();
        // HCSPARAMS2 scratchpad count (§5.3.4): Hi = bits[25:21], Lo = bits[31:27];
        // total = (Hi << 5) | Lo.  (Reversing Hi/Lo is a common mistake.)
        let sp_hi = (hcsparams2 >> 21) & 0x1f;
        let sp_lo = (hcsparams2 >> 27) & 0x1f;
        let max_scratchpad =
            usize::try_from((sp_hi << 5) | sp_lo).map_err(|_| XhciErr::Overflow)?;

        log::info!(
            "xHCI: {name}: HCIVERSION={hci_version:#06x} CAPLENGTH={caplength:#04x} \
             HCSPARAMS1={hcsparams1:#010x} HCSPARAMS2={hcsparams2:#010x} \
             HCCPARAMS1={hccparams1:#010x} DBOFF={dboff:#x} RTSOFF={rtsoff:#x}"
        );

        let core = HcCore {
            op: cap.window(caplength)?,
            ir0: cap.window(rtsoff)?.window(regs::ir::BASE)?,
            db: cap.window(dboff)?,
            cmd_ring: CommandRing::new(NUMA_NODE)?,
            evt_ring: EventRing::new(NUMA_NODE)?,
        };

        Ok(Self {
            name,
            core,
            dcbaa: Dcbaa::new(NUMA_NODE)?,
            max_slots,
            max_scratchpad,
            _scratchpad: Vec::new(),
        })
    }

    // -------------------------------------------------------------------------
    // Initialization sequence (xHCI spec §4.2)
    // -------------------------------------------------------------------------

    fn reset(&mut self) -> Result<(), XhciErr> {
        let op = self.core.op;
        // Wait for CNR to clear (set on power-on until internal init completes).
        op.poll32(regs::op::USBSTS, regs::op::STS_CNR, 0, STATE_POLL_ITERS)
            .inspect_err(|_| log::error!("xHCI: {}: CNR did not clear", self.name))?;

        // Halt the controller if it is currently running.
        let cmd = op.read32(regs::op::USBCMD)?;
        if cmd & regs::op::CMD_RUN_STOP != 0 {
            op.write32(regs::op::USBCMD, cmd & !regs::op::CMD_RUN_STOP)?;
            op.poll32(
                regs::op::USBSTS,
                regs::op::STS_HCH,
                regs::op::STS_HCH,
                STATE_POLL_ITERS,
            )
            .inspect_err(|_| log::error!("xHCI: {}: controller did not halt", self.name))?;
        }

        // Issue HCRST and wait for it to self-clear, then wait for CNR.
        let cmd = op.read32(regs::op::USBCMD)?;
        op.write32(regs::op::USBCMD, cmd | regs::op::CMD_HCRST)?;
        op.poll32(regs::op::USBCMD, regs::op::CMD_HCRST, 0, STATE_POLL_ITERS)
            .inspect_err(|_| log::error!("xHCI: {}: HCRST did not self-clear", self.name))?;
        op.poll32(regs::op::USBSTS, regs::op::STS_CNR, 0, STATE_POLL_ITERS)
            .inspect_err(|_| log::error!("xHCI: {}: CNR did not clear after reset", self.name))?;
        log::info!("xHCI: {}: reset complete", self.name);
        Ok(())
    }

    fn program_rings(&mut self) -> Result<(), XhciErr> {
        let op = self.core.op;
        let ir0 = self.core.ir0;

        // MaxSlotsEn — allow all discovered slots.
        op.write32(regs::op::CONFIG, u32::from(self.max_slots))?;

        let dcbaa = self.dcbaa.phys_base()?;
        op.write64(regs::op::DCBAAP_LO, regs::op::DCBAAP_HI, dcbaa)?;

        // CRCR — command ring base + initial Ring Cycle State = 1.
        let crcr = self.core.cmd_ring.phys_base()?;
        op.write64(
            regs::op::CRCR_LO,
            regs::op::CRCR_HI,
            crcr | u64::from(regs::op::CRCR_RCS),
        )?;

        // Interrupter 0: ERSTSZ, ERSTBA, ERDP.
        ir0.write32(regs::ir::ERSTSZ, 1)?;
        let erst = self.core.evt_ring.erst_phys()?;
        ir0.write64(regs::ir::ERSTBA_LO, regs::ir::ERSTBA_HI, erst)?;
        let erdp = self.core.evt_ring.seg_phys()?;
        ir0.write64(regs::ir::ERDP_LO, regs::ir::ERDP_HI, erdp)?;

        let iman = ir0.read32(regs::ir::IMAN)?;
        ir0.write32(regs::ir::IMAN, iman | regs::ir::IMAN_IE)?;

        log::info!(
            "xHCI: {}: dcbaa={dcbaa:#018x} crcr={crcr:#018x} erst={erst:#018x} erdp={erdp:#018x}",
            self.name
        );
        Ok(())
    }

    /// Allocate scratchpad pages and point DCBAA[0] to them (§4.20).
    fn init_scratchpad(&mut self) -> Result<(), XhciErr> {
        let n = self.max_scratchpad;
        log::info!("xHCI: {}: scratchpad count={n}", self.name);
        if n == 0 {
            return Ok(());
        }
        if n > MAX_SCRATCHPAD {
            log::error!(
                "xHCI: {}: scratchpad count {n} > {MAX_SCRATCHPAD}",
                self.name
            );
            return Err(XhciErr::Overflow);
        }

        let mut array = new_page()?;
        let mut pages = Vec::new();
        pages
            .try_reserve_exact(n.checked_add(1).ok_or(XhciErr::Overflow)?)
            .map_err(|_| XhciErr::DmaAlloc)?;
        for entry in array.as_mut().as_chunks_mut::<8>().0.iter_mut().take(n) {
            let page = new_page()?;
            *entry = phys_of(&page)?.to_le_bytes();
            pages.push(page);
        }

        let array_phys = phys_of(&array)?;
        self.dcbaa.set(0, array_phys)?;
        pages.push(array);
        self._scratchpad = pages;
        log::info!(
            "xHCI: {}: scratchpad array phys={array_phys:#018x}",
            self.name
        );
        Ok(())
    }

    /// Set Run/Stop with interrupts disabled (the driver is polled).
    fn start(&mut self) -> Result<(), XhciErr> {
        let op = self.core.op;
        let cmd = (op.read32(regs::op::USBCMD)? | regs::op::CMD_RUN_STOP | regs::op::CMD_HSEE)
            & !regs::op::CMD_INTE;
        op.write32(regs::op::USBCMD, cmd)?;
        // HCHalted must deassert once the controller is running.
        op.poll32(regs::op::USBSTS, regs::op::STS_HCH, 0, STATE_POLL_ITERS)
            .inspect_err(|_| log::error!("xHCI: {}: controller did not start", self.name))?;
        log::info!("xHCI: {}: controller running (polled)", self.name);
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Enumeration
    // -------------------------------------------------------------------------

    /// Check that the command ring works before touching any port.
    fn boot_enumerate(&mut self) -> Result<(), XhciErr> {
        // If a No-Op times out, every later command would too.
        self.core
            .command(Trb {
                param: 0,
                status: 0,
                ctrl: trb_type::NOOP_CMD,
            })
            .inspect_err(|e| log::error!("xHCI: {}: NOOP command failed: {e:?}", self.name))?;
        log::info!(
            "xHCI: {}: NOOP command OK — command ring is alive",
            self.name
        );
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// PCIe device
// ---------------------------------------------------------------------------

pub struct XhciDevice {
    name: String,
    /// Controller state.  Owns the DMA memory the controller keeps using, so it
    /// lives as long as the device; it is not accessed after `attach()`.
    _hc: UnsafeCell<Controller>,
}

impl PCIeDevice for XhciDevice {
    fn device_name(&self) -> Cow<'static, str> {
        Cow::Owned(self.name.clone())
    }
}

// SAFETY: `name` is immutable after construction and `_hc` is never accessed
// after `attach()` returns.  The DMA pools and MMIO windows it owns are plain
// addresses that may move between CPUs.
unsafe impl Send for XhciDevice {}
// SAFETY: see the `Send` impl; no `&self` method touches `_hc`.
unsafe impl Sync for XhciDevice {}

/// Attach an xHCI host controller discovered during PCIe enumeration.
pub(super) fn attach(
    mut info: PCIeInfo,
) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    log::info!("xHCI: attaching {info}");

    info.map_bar()
        .map_err(|_| PCIeDeviceErr::PageTableFailure)?;
    info.read_capability();
    info.disable_legacy_interrupt();

    let cap = Mmio::from_bar(info.get_bar(0)).map_err(|e| {
        log::error!("xHCI: BAR[0] not usable: {e:?}");
        PCIeDeviceErr::BARFailure
    })?;

    let mut hc = Controller::new(cap, format!("{} xHCI", info.get_bdf()))?;
    hc.reset()?;
    // Bus Master may be cleared by HCRST or at ExitBootServices; the controller
    // needs it to DMA into the event ring.
    info.enable_bus_master();
    if !info
        .read_status_command()
        .contains(StatusCommand::BUS_MASTER)
    {
        log::error!("xHCI: {}: BUS_MASTER NOT set — DMA will fail", hc.name);
        return Err(PCIeDeviceErr::InitFailure);
    }
    hc.program_rings()?;
    hc.init_scratchpad()?;
    hc.start()?;
    hc.boot_enumerate()?;

    Ok(Arc::new(XhciDevice {
        name: hc.name.clone(),
        _hc: UnsafeCell::new(hc),
    }))
}
