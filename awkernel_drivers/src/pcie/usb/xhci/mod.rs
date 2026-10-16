//! xHCI host controller driver: boot-time USB enumeration.
//!
//! The driver is fully polled (USBCMD.INTE = 0).
//!
//! Path classification:
//! - Non-RT: [`attach`] and everything it calls (controller reset, port reset,
//!   enumeration).  Runs once at boot; allocates DMA pages and busy-waits with
//!   bounded polling budgets.

use alloc::{borrow::Cow, format, string::String, sync::Arc, vec::Vec};
use core::{cell::UnsafeCell, mem::ManuallyDrop, ptr::read_volatile};

use awkernel_lib::{addr::Addr, dma_pool::DMAPool};

use super::super::{
    mmio::{Mmio, MmioErr},
    registers::StatusCommand,
    PCIeDevice, PCIeDeviceErr, PCIeInfo,
};

mod regs;
mod ring;

use regs::{completion, trb_flag, trb_type};
use ring::{publish, CommandRing, Dcbaa, EventRing, TransferRing, Trb};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Polling budget for controller state transitions (USBSTS / USBCMD / PORTSC).
const STATE_POLL_ITERS: u32 = 1_000_000;
/// Polling budget for one command or transfer completion event.
const COMPLETION_POLL_ITERS: u32 = 2_000_000;
/// A control transfer reports at most a Short Packet (Data Stage) followed by
/// the Status Stage event; allow one spare event.
const MAX_CTRL_EVENTS: usize = 3;
/// VBUS stabilization / device connect wait before scanning ports.
const PORT_SETTLE_USEC: u64 = 500_000;

/// All DMA allocations go to NUMA node 0.
const NUMA_NODE: usize = 0;
const PAGE_SIZE: usize = 4096;
type Page = [u8; PAGE_SIZE];

/// Scratchpad pointer array: one 8-byte entry per page, in one DMA page.
const MAX_SCRATCHPAD: usize = PAGE_SIZE / 8;

/// Device Context Index of the default control endpoint (EP0).
const EP0_DCI: u8 = 1;

/// Endpoint Context DW1: CErr = 3, EP Type = Control (4).
const EP_CTX_CONTROL: u8 = (3 << 1) | (4 << 3);

/// PORTSC speed values (xHCI spec §7.2.2.1.1 default PSI).
const SPEED_LOW: u32 = 2;
const SPEED_HIGH: u32 = 3;
const SPEED_SUPER: u32 = 4;
const SPEED_SUPER_PLUS: u32 = 5;
const PORTSC_SPEED_SHIFT: u32 = 10;

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
    InvalidPort,
    InvalidSlot,
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

/// TRB ctrl bits for Slot ID (ctrl[31:24]) and Endpoint ID (ctrl[20:16]).
fn ctrl_slot_ep(slot: u8, dci: u8) -> u32 {
    u32::from_le_bytes([0, 0, dci, slot])
}

/// Write a little-endian u32 into an Input Context page.
fn ctx_write32(page: &mut Page, off: usize, val: u32) -> Result<(), XhciErr> {
    let end = off.checked_add(4).ok_or(XhciErr::Overflow)?;
    page.get_mut(off..end)
        .ok_or(XhciErr::Overflow)?
        .copy_from_slice(&val.to_le_bytes());
    Ok(())
}

fn new_page() -> Result<DMAPool<Page>, XhciErr> {
    let mut page = DMAPool::<Page>::new(NUMA_NODE, 1).ok_or(XhciErr::DmaAlloc)?;
    page.as_mut().fill(0);
    Ok(page)
}

// ---------------------------------------------------------------------------
// USB control requests
// ---------------------------------------------------------------------------

/// USB SETUP packet (USB 2.0 spec §9.3).
#[derive(Clone, Copy)]
struct SetupPacket {
    request_type: u8,
    request: u8,
    value: u16,
    index: u16,
    length: u16,
}

impl SetupPacket {
    /// Pack into the 8-byte immediate data of a Setup Stage TRB.
    fn to_param(self) -> u64 {
        let [rt, rq] = [self.request_type, self.request];
        let [v0, v1] = self.value.to_le_bytes();
        let [i0, i1] = self.index.to_le_bytes();
        let [l0, l1] = self.length.to_le_bytes();
        u64::from_le_bytes([rt, rq, v0, v1, i0, i1, l0, l1])
    }

    /// True when the data stage (if any) moves data from device to host.
    fn is_in(&self) -> bool {
        self.request_type & 0x80 != 0
    }
}

const RT_DEV_IN: u8 = 0x80; // D→H, Standard, Device

const REQ_GET_DESCRIPTOR: u8 = 6;

const DESC_DEVICE: u16 = 0x0100;
const DEVICE_DESC_LEN: u16 = 18;

// ---------------------------------------------------------------------------
// Device state
// ---------------------------------------------------------------------------

/// Device Descriptor fields kept after enumeration.
#[derive(Clone, Copy, Default)]
struct DeviceDescriptor {
    vendor: u16,
    product: u16,
    bcd_device: u16,
}

/// One addressed USB device.
///
/// Always held in `ManuallyDrop`: once a slot is addressed, the controller keeps
/// pointers to the Device Context and the rings, so freeing them would let the
/// controller DMA into reused memory.  A few pages per enumerated device are
/// leaked at boot instead.
struct UsbDevice {
    slot: u8,
    port: u8,
    /// PORTSC speed value (bits [13:10], already shifted down).
    speed: u32,
    ep0: TransferRing,
    /// Output Device Context, referenced by DCBAA[slot].
    _ctx: DMAPool<Page>,
    /// Data-stage buffer shared by all control transfers of this device.
    ctrl_buf: DMAPool<Page>,
    desc: DeviceDescriptor,
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

    /// Consume and discard every pending event (at most one ring's worth).
    fn drain_events(&mut self) -> Result<(), XhciErr> {
        for _ in 0..ring::RING_SIZE {
            if self.evt_ring.dequeue()?.is_none() {
                break;
            }
            self.update_erdp()?;
        }
        Ok(())
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

    /// Wait for the Status Stage of a control transfer (Short Packet on the
    /// Data Stage is skipped).
    fn wait_transfer(&mut self, max_events: usize) -> Result<(), XhciErr> {
        for _ in 0..max_events {
            match self.wait_event(trb_type::TRANSFER_EVENT)?.completion_code() {
                completion::SUCCESS => return Ok(()),
                completion::SHORT_PACKET => continue,
                code => return Err(XhciErr::Completion(code)),
            }
        }
        Err(XhciErr::Completion(completion::SHORT_PACKET))
    }

    /// Run one control transfer on EP0 of `dev`.  The data stage (if
    /// `setup.length > 0`) uses `dev.ctrl_buf`.
    fn control(&mut self, dev: &mut UsbDevice, setup: SetupPacket) -> Result<(), XhciErr> {
        let is_in = setup.is_in();
        let has_data = setup.length > 0;
        let trt = match (has_data, is_in) {
            (false, _) => trb_flag::TRT_NO_DATA,
            (true, true) => trb_flag::TRT_IN,
            (true, false) => trb_flag::TRT_OUT,
        };

        dev.ep0.enqueue(Trb {
            param: setup.to_param(),
            status: 8, // setup packet size
            ctrl: trb_type::SETUP_STAGE | trb_flag::IDT | trt,
        })?;
        if has_data {
            dev.ep0.enqueue(Trb {
                param: phys_of(&dev.ctrl_buf)?,
                status: u32::from(setup.length),
                ctrl: trb_type::DATA_STAGE | if is_in { trb_flag::DIR_IN } else { 0 },
            })?;
        }
        // Status Stage runs opposite to the data stage (IN when there is none).
        let status_dir = if has_data && is_in {
            0
        } else {
            trb_flag::DIR_IN
        };
        dev.ep0.enqueue(Trb {
            param: 0,
            status: 0,
            ctrl: trb_type::STATUS_STAGE | trb_flag::IOC | status_dir,
        })?;

        self.ring_doorbell(dev.slot, EP0_DCI)?;
        self.wait_transfer(MAX_CTRL_EVENTS)
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
    max_ports: u8,
    /// Context size in bytes: 32 (CSZ=0) or 64 (CSZ=1).
    ctx_size: usize,
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
        let [max_slots, _, _, max_ports] = hcsparams1.to_le_bytes();
        // HCSPARAMS2 scratchpad count (§5.3.4): Hi = bits[25:21], Lo = bits[31:27];
        // total = (Hi << 5) | Lo.  (Reversing Hi/Lo is a common mistake.)
        let sp_hi = (hcsparams2 >> 21) & 0x1f;
        let sp_lo = (hcsparams2 >> 27) & 0x1f;
        let max_scratchpad =
            usize::try_from((sp_hi << 5) | sp_lo).map_err(|_| XhciErr::Overflow)?;
        let ctx_size: usize = if hccparams1 & regs::cap::HCC_CSZ != 0 {
            64
        } else {
            32
        };

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
            max_ports,
            ctx_size,
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
    // Ports
    // -------------------------------------------------------------------------

    /// PORTSC offset for 1-based port number `port`.
    fn portsc_offset(&self, port: u8) -> Result<usize, XhciErr> {
        if port == 0 || port > self.max_ports {
            return Err(XhciErr::InvalidPort);
        }
        usize::from(port)
            .checked_sub(1)
            .and_then(|p| p.checked_mul(regs::port::STRIDE))
            .and_then(|o| o.checked_add(regs::port::BASE))
            .ok_or(XhciErr::Overflow)
    }

    fn read_portsc(&self, port: u8) -> Result<u32, XhciErr> {
        Ok(self.core.op.read32(self.portsc_offset(port)?)?)
    }

    fn write_portsc(&self, port: u8, val: u32) -> Result<(), XhciErr> {
        Ok(self.core.op.write32(self.portsc_offset(port)?, val)?)
    }

    /// Reset `port` and wait for Port Reset Change (RW1CS bits handled per spec).
    fn reset_port(&mut self, port: u8) -> Result<(), XhciErr> {
        // Pre-clear stale change bits (write 1) while setting PR; keep PP, avoid PED.
        let portsc = self.read_portsc(port)?;
        self.write_portsc(
            port,
            (portsc & !regs::port::PED) | (portsc & regs::port::CHANGE_BITS) | regs::port::PR,
        )?;
        self.core.op.poll32(
            self.portsc_offset(port)?,
            regs::port::PRC,
            regs::port::PRC,
            COMPLETION_POLL_ITERS,
        )?;
        // Clear PRC (and any other change bits) by writing 1 to them.
        let portsc = self.read_portsc(port)?;
        self.write_portsc(
            port,
            (portsc & !(regs::port::PED | regs::port::PR)) | (portsc & regs::port::CHANGE_BITS),
        )?;
        self.core.drain_events()
    }

    // -------------------------------------------------------------------------
    // Enumeration
    // -------------------------------------------------------------------------

    /// Scan all ports and enumerate every connected device.
    fn boot_enumerate(&mut self) -> Result<(), XhciErr> {
        // xHCI §4.19.1.1: with a port power controller, software must set PP=1;
        // PR=1 on an unpowered port is silently ignored.
        for port in 1..=self.max_ports {
            let portsc = self.read_portsc(port)?;
            if portsc & regs::port::PP == 0 {
                self.write_portsc(
                    port,
                    (portsc & !(regs::port::PED | regs::port::PR))
                        | (portsc & regs::port::CHANGE_BITS)
                        | regs::port::PP,
                )?;
                log::info!("xHCI: {}: port {port} PP was 0, powered on", self.name);
            }
        }

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

        awkernel_lib::delay::wait_microsec(PORT_SETTLE_USEC);
        self.core.drain_events()?;

        // Snapshot connected ports first: resetting one port must not change
        // which ports we visit.
        let mut connected = Vec::new();
        for port in 1..=self.max_ports {
            if self.read_portsc(port)? & regs::port::CCS != 0 {
                connected.push(port);
            }
        }
        if connected.is_empty() {
            log::info!("xHCI: {}: no device found at boot", self.name);
            return Ok(());
        }

        for port in connected {
            log::info!("xHCI: {}: device detected on port {port}", self.name);
            if let Err(e) = self.enumerate_port(port) {
                log::error!("xHCI: {}: port {port} enumeration failed: {e:?}", self.name);
            }
            // The device is leaked (see `UsbDevice`).  Stale transfer events
            // would corrupt the next port's enumeration.
            self.core.drain_events()?;
        }
        Ok(())
    }

    /// Reset `port`, enable a slot, address the device and read its Device Descriptor.
    fn enumerate_port(&mut self, port: u8) -> Result<ManuallyDrop<UsbDevice>, XhciErr> {
        self.reset_port(port)?;

        let slot = self
            .core
            .command(Trb {
                param: 0,
                status: 0,
                ctrl: trb_type::ENABLE_SLOT,
            })?
            .slot_id();
        if slot == 0 || slot > self.max_slots {
            return Err(XhciErr::InvalidSlot);
        }
        log::info!("xHCI: {}: slot {slot} assigned for port {port}", self.name);

        let speed = (self.read_portsc(port)? & regs::port::SPEED_MASK) >> PORTSC_SPEED_SHIFT;
        let ctx = new_page()?;
        self.dcbaa.set(slot, phys_of(&ctx)?)?;
        let mut dev = ManuallyDrop::new(UsbDevice {
            slot,
            port,
            speed,
            ep0: TransferRing::new(NUMA_NODE)?,
            _ctx: ctx,
            ctrl_buf: new_page()?,
            desc: DeviceDescriptor::default(),
        });

        self.address_device(&mut dev)?;
        log::info!("xHCI: {}: slot {slot} addressed", self.name);
        self.read_device_descriptor(&mut dev)?;
        Ok(dev)
    }

    /// Issue Address Device (BSR=0, so the controller sends SET_ADDRESS).
    fn address_device(&mut self, dev: &mut UsbDevice) -> Result<(), XhciErr> {
        let ctx = self.ctx_size;
        // EP0 max packet size by speed.  Full Speed devices may use 8..=64; 64
        // avoids Babble Detected on FS devices whose real MaxPacketSize0 is 64
        // (e.g. PL2303HX/HXN) and is accepted for smaller ones as well.
        let max_pkt: u16 = match dev.speed {
            SPEED_LOW => 8,
            SPEED_HIGH => 64,
            SPEED_SUPER | SPEED_SUPER_PLUS => 512,
            _ => 64,
        };
        let ep0_phys = dev.ep0.phys_base()?;

        let mut input = ManuallyDrop::new(new_page()?);
        {
            let page = input.as_mut();
            // Input Control Context: Add A0 (slot) + A1 (EP0).
            ctx_write32(page, 4, 0b11)?;
            // Slot Context: Speed[23:20], Context Entries[31:27] = 1, Root Hub Port[23:16].
            let speed = u8::try_from(dev.speed).map_err(|_| XhciErr::Overflow)?;
            ctx_write32(page, ctx, u32::from_le_bytes([0, 0, speed << 4, 1 << 3]))?;
            ctx_write32(
                page,
                ctx.checked_add(4).ok_or(XhciErr::Overflow)?,
                u32::from_le_bytes([0, 0, dev.port, 0]),
            )?;
            // EP0 Context (DCI 1).
            let ep = ctx.checked_mul(2).ok_or(XhciErr::Overflow)?;
            write_ep_context(page, ep, EP_CTX_CONTROL, max_pkt, ep0_phys, 8)?;
        }

        let result = self.core.command(Trb {
            param: phys_of(&input)?,
            status: 0,
            ctrl: trb_type::ADDRESS_DEVICE | ctrl_slot_ep(dev.slot, 0),
        });
        release_unless_timeout(input, &result);
        result.map(|_| ())
    }

    /// GET_DESCRIPTOR(Device) and cache the fields used later.
    fn read_device_descriptor(&mut self, dev: &mut UsbDevice) -> Result<(), XhciErr> {
        self.core.control(
            dev,
            SetupPacket {
                request_type: RT_DEV_IN,
                request: REQ_GET_DESCRIPTOR,
                value: DESC_DEVICE,
                index: 0,
                length: DEVICE_DESC_LEN,
            },
        )?;
        let [_, _, usb_lo, usb_hi, class, sub, proto, _, v_lo, v_hi, p_lo, p_hi, d_lo, d_hi, ..] =
            read_ctrl_buf::<18>(dev)?;
        dev.desc = DeviceDescriptor {
            vendor: u16::from_le_bytes([v_lo, v_hi]),
            product: u16::from_le_bytes([p_lo, p_hi]),
            bcd_device: u16::from_le_bytes([d_lo, d_hi]),
        };
        log::info!(
            "xHCI: {}: slot {} — USB {:x}.{:02x} VID={:#06x} PID={:#06x} \
             class={class:#04x}/{sub:#04x}/{proto:#04x} bcdDevice={:#06x}",
            self.name,
            dev.slot,
            usb_hi,
            usb_lo,
            dev.desc.vendor,
            dev.desc.product,
            dev.desc.bcd_device,
        );
        Ok(())
    }
}

/// Write one Endpoint Context (DW1..DW4) at byte offset `off` of an Input Context.
fn write_ep_context(
    page: &mut Page,
    off: usize,
    ep_type: u8,
    max_pkt: u16,
    ring_phys: u64,
    avg_trb_len: u32,
) -> Result<(), XhciErr> {
    let at = |delta: usize| off.checked_add(delta).ok_or(XhciErr::Overflow);
    let [mp_lo, mp_hi] = max_pkt.to_le_bytes();
    // DW1: CErr / EP Type in the low byte, Max Packet Size in [31:16].
    ctx_write32(page, at(4)?, u32::from_le_bytes([ep_type, 0, mp_lo, mp_hi]))?;
    // DW2/DW3: TR Dequeue Pointer with DCS = 1 (matches the ring's initial cycle).
    ctx_write32(page, at(8)?, lo32(ring_phys) | trb_flag::CYCLE)?;
    ctx_write32(page, at(12)?, hi32(ring_phys))?;
    // DW4: Average TRB Length.
    ctx_write32(page, at(16)?, avg_trb_len)
}

/// Free a transient Input Context unless the command timed out (in which case
/// the controller may still read it later).
fn release_unless_timeout<T, R>(buf: ManuallyDrop<DMAPool<T>>, result: &Result<R, XhciErr>) {
    if !matches!(result, Err(XhciErr::Timeout)) {
        drop(ManuallyDrop::into_inner(buf));
    }
}

/// Copy the first `N` bytes of `dev.ctrl_buf` written by the controller.
fn read_ctrl_buf<const N: usize>(dev: &UsbDevice) -> Result<[u8; N], XhciErr> {
    let bytes = dev
        .ctrl_buf
        .as_ref()
        .first_chunk::<N>()
        .ok_or(XhciErr::Overflow)?;
    // SAFETY: `bytes` points into the live DMA page; volatile because the
    // controller wrote it via DMA.
    Ok(unsafe { read_volatile(bytes) })
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
