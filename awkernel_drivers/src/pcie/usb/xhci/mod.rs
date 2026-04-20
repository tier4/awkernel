use alloc::{borrow::Cow, boxed::Box, format, string::String, sync::Arc};
use awkernel_lib::{addr::{virt_addr::VirtAddr, Addr}, dma_pool::DMAPool};

// super       = crate::pcie::usb
// super::super = crate::pcie  (where PCIeDevice, PCIeDeviceErr, PCIeInfo, base_address live)
use super::super::{
    base_address::BaseAddress, PCIeDevice, PCIeDeviceErr, PCIeInfo,
};

mod cdc_acm;
mod fat32;
mod msc;
mod pl2303;
mod regs;
mod ring;

use core::sync::atomic::{AtomicBool, AtomicU32, AtomicU8, AtomicUsize, Ordering};

use ring::{CommandRing, Dcbaa, EventRing, TransferRing, Trb};

// ---------------------------------------------------------------------------
// Phase 9: global CDC-ACM console writer
//
// After the xHCI driver configures a CDC-ACM device it stores a raw pointer
// to the (heap-pinned) XhciDevice here.  xhci_usb_serial_puts() uses this
// pointer to write strings via bulk OUT without going through Arc/dyn dispatch.
//
// Safety contract:
//   - CDC_DEV_PTR is written exactly once (in attach()) after Arc::new(dev)
//     pins the device on the heap; the Arc is never dropped in kernel lifetime.
//   - CDC_LOCK prevents concurrent/reentrant access.
// ---------------------------------------------------------------------------

static CDC_DEV_PTR: AtomicUsize = AtomicUsize::new(0);
static CDC_SLOT:    AtomicU8    = AtomicU8::new(0);
/// Spinlock + reentrancy guard: if already held (recursive log call inside a
/// CDC write), skip rather than deadlock.
static CDC_LOCK:    AtomicBool  = AtomicBool::new(false);

/// Incremented each time start_controller() succeeds.
static XHCI_STARTED: AtomicUsize = AtomicUsize::new(0);
/// Incremented for every port with CCS=1 seen across all boot_enumerate() calls.
static XHCI_CCS_SEEN: AtomicUsize = AtomicUsize::new(0);
/// Incremented when enumerate_port() returns Ok (device was addressed + described).
static XHCI_ENUM_OK: AtomicUsize = AtomicUsize::new(0);
/// Set when try_setup_pl2303() sees VID:PID 067b:23xx (PL2303 chip identified).
static XHCI_PL2303_VID_SEEN:  AtomicBool = AtomicBool::new(false);
/// Set after get_config_descriptor() succeeds inside try_setup_pl2303().
static XHCI_PL2303_GOT_CFG:   AtomicBool = AtomicBool::new(false);
/// Set after find_bulk_endpoints() finds IN+OUT pair inside try_setup_pl2303().
static XHCI_PL2303_GOT_EPS:   AtomicBool = AtomicBool::new(false);
/// Set after set_configuration() succeeds inside try_setup_pl2303().
static XHCI_PL2303_SET_CFG:   AtomicBool = AtomicBool::new(false);
/// Set after configure_bulk_endpoints() (CONFIGURE_EP) succeeds.
static XHCI_PL2303_CFG_EPS:   AtomicBool = AtomicBool::new(false);
/// Set after pl2303_init_seq() completes successfully.
static XHCI_PL2303_INIT_SEQ:  AtomicBool = AtomicBool::new(false);
/// Incremented when port reset (PRC polling) succeeds.
static XHCI_PORT_RESET_OK: AtomicUsize = AtomicUsize::new(0);
/// Incremented when Enable Slot command completes with code=1.
static XHCI_SLOT_ENABLED: AtomicUsize = AtomicUsize::new(0);
/// 0=not attempted, 1=OK, 2=failed/timeout
static XHCI_NOOP_RESULT: AtomicU32 = AtomicU32::new(0);
/// USBSTS value captured at the first command timeout; u32::MAX = no timeout yet.
static XHCI_USBSTS_ON_SLOT_FAIL: AtomicU32 = AtomicU32::new(u32::MAX);
/// Set to true if BUS_MASTER bit confirmed set after enable_bus_master().
static XHCI_BUS_MASTER_OK: AtomicBool = AtomicBool::new(false);

/// Returns true if a CDC-ACM or PL2303 device was found and registered.
pub fn is_cdc_registered() -> bool {
    CDC_DEV_PTR.load(Ordering::Acquire) != 0
}

/// Returns true if at least one xHCI controller successfully started.
pub fn xhci_any_started() -> bool {
    XHCI_STARTED.load(Ordering::Relaxed) > 0
}

/// Returns true if at least one USB device (CCS=1) was seen during enumeration.
pub fn xhci_any_device_seen() -> bool {
    XHCI_CCS_SEEN.load(Ordering::Relaxed) > 0
}

/// Returns true if at least one port reset completed (PRC=1 seen).
pub fn xhci_any_port_reset_ok() -> bool {
    XHCI_PORT_RESET_OK.load(Ordering::Relaxed) > 0
}

/// Returns true if at least one Enable Slot command completed successfully.
pub fn xhci_any_slot_enabled() -> bool {
    XHCI_SLOT_ENABLED.load(Ordering::Relaxed) > 0
}

/// Returns true if at least one device was fully addressed (enumerate_port returned Ok).
pub fn xhci_any_enum_ok() -> bool {
    XHCI_ENUM_OK.load(Ordering::Relaxed) > 0
}

/// Returns true if PL2303 VID:PID (067b:23xx) was matched during setup.
pub fn xhci_pl2303_vid_seen() -> bool { XHCI_PL2303_VID_SEEN.load(Ordering::Relaxed) }
pub fn xhci_pl2303_got_cfg()  -> bool { XHCI_PL2303_GOT_CFG.load(Ordering::Relaxed) }
pub fn xhci_pl2303_got_eps()  -> bool { XHCI_PL2303_GOT_EPS.load(Ordering::Relaxed) }
pub fn xhci_pl2303_set_cfg()  -> bool { XHCI_PL2303_SET_CFG.load(Ordering::Relaxed) }
pub fn xhci_pl2303_cfg_eps()  -> bool { XHCI_PL2303_CFG_EPS.load(Ordering::Relaxed) }
pub fn xhci_pl2303_init_seq() -> bool { XHCI_PL2303_INIT_SEQ.load(Ordering::Relaxed) }

/// 0 = not attempted, 1 = success, 2 = fail/timeout
pub fn xhci_noop_result() -> u32 {
    XHCI_NOOP_RESULT.load(Ordering::Relaxed)
}
pub fn xhci_bus_master_ok() -> bool {
    XHCI_BUS_MASTER_OK.load(Ordering::Relaxed)
}

/// Returns the USBSTS value captured at the first Enable Slot timeout, if any.
pub fn xhci_usbsts_on_fail() -> Option<u32> {
    let v = XHCI_USBSTS_ON_SLOT_FAIL.load(Ordering::Relaxed);
    if v == u32::MAX { None } else { Some(v) }
}

/// Write `data` to the CDC-ACM USB serial adapter if one has been configured.
/// No-ops when CDC-ACM is unavailable; never blocks more than a USB bulk timeout.
/// Skips silently on reentrant calls (e.g. log from within a CDC write path).
pub fn xhci_usb_serial_puts(data: &str) {
    let ptr = CDC_DEV_PTR.load(Ordering::Acquire);
    if ptr == 0 { return; }

    // Try to acquire the spinlock; skip if already held (reentrancy guard).
    if CDC_LOCK
        .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        return;
    }

    // SAFETY: CDC_DEV_PTR holds the address of an XhciDevice pinned inside an Arc
    // that lives for the kernel's entire lifetime.  CDC_LOCK prevents aliased &mut.
    let dev = unsafe { &mut *(ptr as *mut XhciDevice) };
    let slot = CDC_SLOT.load(Ordering::Relaxed);
    let _ = dev.cdcacm_write(slot, data.as_bytes());

    CDC_LOCK.store(false, Ordering::Release);
}

pub struct XhciDevice {
    name: String,

    // Mapped register region bases (identity-mapped MMIO, virt == phys)
    cap_base: VirtAddr, // BAR[0]
    op_base: VirtAddr,  // BAR[0] + CAPLENGTH
    rt_base: VirtAddr,  // BAR[0] + RTSOFF
    db_base: VirtAddr,  // BAR[0] + DBOFF

    // Controller parameters decoded from HCSPARAMS1
    pub max_slots: u8,
    pub max_ports: u8,
    pub max_interrupters: u16,
    pub hci_version: u16,

    // DMA rings (pre-allocated, zeroed, Link TRB installed)
    cmd_ring: CommandRing,
    evt_ring: EventRing,
    dcbaa: Dcbaa,

    // Scratchpad buffers: HCSPARAMS2[31:27]||[25:21] pages, DCBAA[0] → array of phys ptrs.
    // Must be allocated before R/S=1 on hardware that requires scratchpad (count > 0).
    max_scratchpad: u32,
    scratchpad_array: Option<DMAPool<[u8; 4096]>>,
    scratchpad_bufs: alloc::vec::Vec<DMAPool<[u8; 4096]>>,

    // Context size: 32 bytes (CSZ=0) or 64 bytes (CSZ=1). Decoded from HCCPARAMS1.
    ctx_size: usize,

    // Per-device state populated during enumeration (one device at a time for now).
    dev_slot: Option<u8>,
    ep0_ring: Option<TransferRing>,
    dev_ctx: Option<DMAPool<[u8; 4096]>>,

    // Phase 4: bulk endpoint rings and metadata (set after CONFIGURE_EP).
    bulk_in_ring: Option<TransferRing>,
    bulk_out_ring: Option<TransferRing>,
    bulk_in_ep_id: u8,    // xHCI DCI for bulk IN doorbell
    bulk_out_ep_id: u8,   // xHCI DCI for bulk OUT doorbell
    dev_speed: u8,        // PORTSC speed field cached from enumerate_port
    dev_port: u8,         // 1-based port number cached from enumerate_port
    msc_tag: u32,         // monotonic BOT transaction tag

    // Phase 5: mounted FAT32 volume state (set after fat32_mount).
    fat32: Option<fat32::Fat32>,

    // Phase 6: CDC-ACM serial adapter state (set after try_setup_cdcacm succeeds).
    is_cdcacm: bool,
    cdcacm_ctrl_if: u8,  // bInterfaceNumber of CDC Communication interface (wIndex for class reqs)
    cdcacm_max_pkt: u16, // wMaxPacketSize of the CDC data bulk endpoints

    // Phase 8: pre-allocated DMA buffer for console TX (avoids per-write DMA allocation).
    cdcacm_tx_dma: Option<DMAPool<[u8; 512]>>,

    // PL2303: USB-to-RS232 adapter (Prolific Technology).
    // Shares cdcacm_tx_dma / cdcacm_max_pkt / bulk_{in,out}_ring with CDC-ACM TX path.
    is_pl2303: bool,

    // Device descriptor cache — populated during get_device_descriptor() so that
    // subsequent try_setup_pl2303() can identify the chip type without re-reading.
    dev_vid:      u16,
    dev_pid:      u16,
    dev_bcd:      u16, // bcdDevice
    dev_class:    u8,
    dev_max_pkt0: u8,  // bMaxPacketSize0
}

impl PCIeDevice for XhciDevice {
    fn device_name(&self) -> Cow<'static, str> {
        Cow::Owned(self.name.clone())
    }
}

// SAFETY: VirtAddr is a plain usize used only for MMIO pointer arithmetic; access
// is always done via volatile reads/writes and is single-threaded at init time.
// DMAPool<T> is already Send+Sync.
unsafe impl Send for XhciDevice {}
unsafe impl Sync for XhciDevice {}

/// Attach an xHCI host controller discovered during PCIe enumeration.
pub(super) fn attach(
    mut info: PCIeInfo,
) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    log::info!("xHCI: attaching {}", info);

    // Map the MMIO region(s) declared in BARs.
    info.map_bar().map_err(|_| PCIeDeviceErr::PageTableFailure)?;
    info.read_capability();
    info.disable_legacy_interrupt();

    let cap_base = match info.get_bar(0) {
        Some(BaseAddress::Mmio { addr, .. }) => VirtAddr::new(addr),
        _ => {
            log::error!("xHCI: BAR[0] not found or not MMIO");
            return Err(PCIeDeviceErr::BARFailure);
        }
    };

    let mut dev = XhciDevice::new(cap_base, &info)?;

    log::info!(
        "xHCI: {}: HCIVERSION={:#06x} ports={} slots={} interrupters={}",
        dev.name,
        dev.hci_version,
        dev.max_ports,
        dev.max_slots,
        dev.max_interrupters,
    );
    log::info!(
        "xHCI: cmd_ring_phys={:#018x}  evt_seg_phys={:#018x}  erst_phys={:#018x}",
        dev.cmd_ring.phys_base(),
        dev.evt_ring.seg_phys(),
        dev.evt_ring.erst_phys(),
    );

    // Phase 2: reset → program rings → MSI-X → start
    dev.reset_controller()?;
    // Re-enable Bus Master after HCRST — some controllers clear it during reset,
    // and UEFI may have cleared it at ExitBootServices.  Must be set before
    // start_controller() so the controller can DMA to the event ring.
    info.enable_bus_master();
    // Read back to verify BUS_MASTER actually stuck (some controllers reset it on HCRST).
    if info.read_status_command().contains(
        super::super::registers::StatusCommand::BUS_MASTER,
    ) {
        XHCI_BUS_MASTER_OK.store(true, Ordering::Relaxed);
        log::info!("xHCI: {}: BUS_MASTER confirmed set", dev.name);
    } else {
        log::error!("xHCI: {}: BUS_MASTER NOT set — DMA will fail!", dev.name);
    }
    dev.program_rings();
    dev.init_scratchpad().map_err(|_| PCIeDeviceErr::InitFailure)?;

    // Capture MMIO base values for the interrupt handler closure.
    let op_base_val = dev.op_base.as_usize();
    let rt_base_val = dev.rt_base.as_usize();
    let handler_name = Cow::Owned(dev.name.clone());

    let mut interrupt_ready = false;
    if let Some(msix) = info.get_msix_mut() {
        msix.enable();
        match msix.register_handler(
            handler_name,
            Box::new(move |_vec: u16| {
                // Minimal ISR: clear pending bits so the interrupt line deasserts.
                // Full event processing is added in Phase 3.
                unsafe {
                    // Clear USBSTS.EINT (RW1C).
                    core::ptr::write_volatile(
                        (op_base_val + regs::op::USBSTS) as *mut u32,
                        regs::op::STS_EINT,
                    );
                    // Clear IMAN.IP (RW1C).
                    let ir_base = rt_base_val + regs::ir::BASE;
                    let iman =
                        core::ptr::read_volatile((ir_base + regs::ir::IMAN) as *const u32);
                    core::ptr::write_volatile(
                        (ir_base + regs::ir::IMAN) as *mut u32,
                        iman | regs::ir::IMAN_IP,
                    );
                    // Clear ERDP.EHB (RW1C; preserve dequeue pointer).
                    let erdp =
                        core::ptr::read_volatile((ir_base + regs::ir::ERDP_LO) as *const u32);
                    core::ptr::write_volatile(
                        (ir_base + regs::ir::ERDP_LO) as *mut u32,
                        erdp | regs::ir::ERDP_EHB,
                    );
                }
            }),
            0, // PCIe segment 0
            0, // target: BSP (CPU 0)
            0, // MSI-X table entry 0
        ) {
            Ok(_irq) => {
                log::info!("xHCI: {}: MSI-X interrupt registered", dev.name);
                interrupt_ready = true;
            }
            Err(e) => log::warn!("xHCI: {}: MSI-X registration failed: {:?}", dev.name, e),
        }
    } else {
        log::warn!("xHCI: {}: no MSI-X capability, running polled", dev.name);
    }

    dev.start_controller(interrupt_ready)?;
    XHCI_STARTED.fetch_add(1, Ordering::Relaxed);

    // Synchronous boot-time enumeration: find and address any device already connected.
    dev.boot_enumerate();

    // Phase 9: pin the device on the heap and, if a CDC-ACM serial adapter was
    // found during enumeration, register its pointer for the console write path.
    let arc: alloc::sync::Arc<XhciDevice> = alloc::sync::Arc::new(dev);
    if arc.is_cdcacm || arc.is_pl2303 {
        if let Some(slot) = arc.dev_slot {
            // Arc::as_ptr gives a stable address for the lifetime of the Arc.
            CDC_DEV_PTR.store(alloc::sync::Arc::as_ptr(&arc) as usize, Ordering::Release);
            CDC_SLOT.store(slot, Ordering::Release);
            let kind = if arc.is_cdcacm { "CDC-ACM" } else { "PL2303" };
            log::info!("xHCI: {} console writer registered (slot={})", kind, slot);
        }
    }
    Ok(arc)
}

impl XhciDevice {
    fn new(cap_base: VirtAddr, info: &PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        // SAFETY: BAR[0] was mapped by map_bar(); all offsets are within xHCI spec §5.3.
        let caplength = unsafe { rd8(cap_base, regs::cap::CAPLENGTH) } as usize;
        let hci_version = unsafe { rd16(cap_base, regs::cap::HCIVERSION) };
        let hcsparams1 = unsafe { rd32(cap_base, regs::cap::HCSPARAMS1) };
        let hcsparams2 = unsafe { rd32(cap_base, regs::cap::HCSPARAMS2) };
        let hccparams1 = unsafe { rd32(cap_base, regs::cap::HCCPARAMS1) };
        let dboff = unsafe { rd32(cap_base, regs::cap::DBOFF) } as usize;
        let rtsoff = unsafe { rd32(cap_base, regs::cap::RTSOFF) } as usize;

        let max_slots = (hcsparams1 & 0xff) as u8;
        let max_interrupters = ((hcsparams1 >> 8) & 0x7ff) as u16;
        let max_ports = (hcsparams1 >> 24) as u8;
        // HCSPARAMS2 scratchpad count (§5.3.4):
        //   Hi = bits[25:21], Lo = bits[31:27]; total = (Hi << 5) | Lo
        // (FreeBSD/Linux both use this order; reversed is a common mistake.)
        let max_scratchpad =
            (((hcsparams2 >> 21) & 0x1f) << 5) | ((hcsparams2 >> 27) & 0x1f);
        // CSZ bit (bit 2) of HCCPARAMS1: 0 = 32-byte contexts, 1 = 64-byte contexts.
        let ctx_size: usize = if hccparams1 & (1 << 2) != 0 { 64 } else { 32 };

        log::debug!(
            "xHCI: CAPLENGTH={caplength:#04x} HCSPARAMS1={hcsparams1:#010x} \
             HCSPARAMS2={hcsparams2:#010x} HCCPARAMS1={hccparams1:#010x} \
             DBOFF={dboff:#010x} RTSOFF={rtsoff:#010x}"
        );

        let op_base = cap_base + caplength;
        let rt_base = cap_base + rtsoff;
        let db_base = cap_base + dboff;

        // Allocate DMA rings on NUMA node 0, then zero and configure them.
        let mut cmd_ring = CommandRing::new(0).ok_or(PCIeDeviceErr::InitFailure)?;
        let mut evt_ring = EventRing::new(0).ok_or(PCIeDeviceErr::InitFailure)?;
        let mut dcbaa = Dcbaa::new(0).ok_or(PCIeDeviceErr::InitFailure)?;
        cmd_ring.init();
        evt_ring.init();
        dcbaa.init();

        let name = format!("{} xHCI", info.get_bdf());

        Ok(XhciDevice {
            name,
            cap_base,
            op_base,
            rt_base,
            db_base,
            max_slots,
            max_ports,
            max_interrupters,
            hci_version,
            cmd_ring,
            evt_ring,
            dcbaa,
            max_scratchpad,
            scratchpad_array: None,
            scratchpad_bufs: alloc::vec::Vec::new(),
            ctx_size,
            dev_slot: None,
            ep0_ring: None,
            dev_ctx: None,
            bulk_in_ring: None,
            bulk_out_ring: None,
            bulk_in_ep_id: 0,
            bulk_out_ep_id: 0,
            dev_speed: 0,
            dev_port: 0,
            msc_tag: 0,
            fat32: None,
            is_cdcacm: false,
            cdcacm_ctrl_if: 0,
            cdcacm_max_pkt: 64,
            cdcacm_tx_dma: None,
            is_pl2303: false,
            dev_vid: 0,
            dev_pid: 0,
            dev_bcd: 0,
            dev_class: 0,
            dev_max_pkt0: 0,
        })
    }

    // --- Operational register accessors (§5.4) ---

    pub fn read_op(&self, offset: usize) -> u32 {
        unsafe { rd32(self.op_base, offset) }
    }

    pub fn write_op(&self, offset: usize, val: u32) {
        unsafe { wr32(self.op_base, offset, val) }
    }

    // --- Interrupter-0 runtime register accessors (§5.5.2) ---

    pub fn read_ir0(&self, offset: usize) -> u32 {
        unsafe { rd32(self.rt_base + regs::ir::BASE, offset) }
    }

    pub fn write_ir0(&self, offset: usize, val: u32) {
        unsafe { wr32(self.rt_base + regs::ir::BASE, offset, val) }
    }

    /// Ring the host-controller command doorbell (slot 0 / HC doorbell). §5.6
    pub fn ring_cmd_doorbell(&self) {
        unsafe { wr32(self.db_base, 0, 0) }
    }

    // -------------------------------------------------------------------------
    // Phase 2: xHCI initialization sequence (spec §4.2)
    // -------------------------------------------------------------------------

    fn poll_usbsts(&self, mask: u32, expected: u32, max_iter: u32) -> bool {
        for _ in 0..max_iter {
            if self.read_op(regs::op::USBSTS) & mask == expected {
                return true;
            }
            core::hint::spin_loop();
        }
        false
    }

    fn poll_usbcmd(&self, mask: u32, expected: u32, max_iter: u32) -> bool {
        for _ in 0..max_iter {
            if self.read_op(regs::op::USBCMD) & mask == expected {
                return true;
            }
            core::hint::spin_loop();
        }
        false
    }

    fn reset_controller(&mut self) -> Result<(), PCIeDeviceErr> {
        // Wait for CNR to clear (set on power-on until internal init completes).
        if !self.poll_usbsts(regs::op::STS_CNR, 0, 1_000_000) {
            log::error!("xHCI: {}: CNR did not clear (power-on timeout)", self.name);
            return Err(PCIeDeviceErr::InitFailure);
        }

        // Halt the controller if it is currently running.
        if self.read_op(regs::op::USBCMD) & regs::op::CMD_RUN_STOP != 0 {
            let cmd = self.read_op(regs::op::USBCMD);
            self.write_op(regs::op::USBCMD, cmd & !regs::op::CMD_RUN_STOP);
            if !self.poll_usbsts(regs::op::STS_HCH, regs::op::STS_HCH, 1_000_000) {
                log::error!("xHCI: {}: controller did not halt", self.name);
                return Err(PCIeDeviceErr::InitFailure);
            }
        }

        // Issue HCRST and wait for it to self-clear, then wait for CNR.
        let cmd = self.read_op(regs::op::USBCMD);
        self.write_op(regs::op::USBCMD, cmd | regs::op::CMD_HCRST);
        if !self.poll_usbcmd(regs::op::CMD_HCRST, 0, 1_000_000) {
            log::error!("xHCI: {}: HCRST did not self-clear", self.name);
            return Err(PCIeDeviceErr::InitFailure);
        }
        if !self.poll_usbsts(regs::op::STS_CNR, 0, 1_000_000) {
            log::error!("xHCI: {}: CNR did not clear after reset", self.name);
            return Err(PCIeDeviceErr::InitFailure);
        }
        log::info!("xHCI: {}: reset complete", self.name);
        Ok(())
    }

    fn program_rings(&mut self) {
        // MaxSlotsEn — allow all discovered slots.
        self.write_op(regs::op::CONFIG, self.max_slots as u32);

        // DCBAAP — device context base address array pointer.
        let dcbaa = self.dcbaa.phys_base();
        self.write_op(regs::op::DCBAAP_LO, dcbaa as u32);
        self.write_op(regs::op::DCBAAP_HI, (dcbaa >> 32) as u32);

        // CRCR — command ring base address + initial Ring Cycle State = 1.
        let crcr = self.cmd_ring.phys_base();
        self.write_op(regs::op::CRCR_LO, crcr as u32 | regs::op::CRCR_RCS);
        self.write_op(regs::op::CRCR_HI, (crcr >> 32) as u32);

        // Interrupter 0: ERSTSZ, ERSTBA, ERDP.
        self.write_ir0(regs::ir::ERSTSZ, 1);
        let erst = self.evt_ring.erst_phys();
        self.write_ir0(regs::ir::ERSTBA_LO, erst as u32);
        self.write_ir0(regs::ir::ERSTBA_HI, (erst >> 32) as u32);
        let erdp = self.evt_ring.seg_phys();
        self.write_ir0(regs::ir::ERDP_LO, erdp as u32);
        self.write_ir0(regs::ir::ERDP_HI, (erdp >> 32) as u32);

        // Enable Interrupter 0 (IE bit in IMAN).
        let iman = self.read_ir0(regs::ir::IMAN);
        self.write_ir0(regs::ir::IMAN, iman | regs::ir::IMAN_IE);

        log::info!(
            "xHCI: {}: dcbaa={:#018x} crcr={:#018x} erst={:#018x} erdp={:#018x}",
            self.name, dcbaa, crcr, erst, erdp,
        );
    }

    /// Allocate scratchpad pages and point DCBAA[0] to them (§4.20).
    /// Must be called after program_rings() and before start_controller().
    fn init_scratchpad(&mut self) -> Result<(), PCIeDeviceErr> {
        let n = self.max_scratchpad as usize;
        log::info!("xHCI: {}: scratchpad count={}", self.name, n);
        if n == 0 {
            return Ok(());
        }

        // Allocate the pointer array (up to 512 entries × 8 bytes fits in one 4 KiB page).
        let mut array = DMAPool::<[u8; 4096]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        for b in array.as_mut().iter_mut() { *b = 0; }

        // Allocate N scratchpad pages; store each physical address into the array.
        let mut bufs: alloc::vec::Vec<DMAPool<[u8; 4096]>> = alloc::vec::Vec::new();
        for i in 0..n {
            let mut buf = DMAPool::<[u8; 4096]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
            for b in buf.as_mut().iter_mut() { *b = 0; }
            let phys = buf.get_phy_addr().as_usize() as u64;
            let off = i * 8;
            array.as_mut()[off..off + 8].copy_from_slice(&phys.to_le_bytes());
            bufs.push(buf);
        }

        // Write array physical address into DCBAA[0].
        let array_phys = array.get_phy_addr().as_usize() as u64;
        self.dcbaa.mem.as_mut()[0] = array_phys;
        log::info!("xHCI: {}: scratchpad array phys={:#018x}", self.name, array_phys);

        self.scratchpad_array = Some(array);
        self.scratchpad_bufs = bufs;
        Ok(())
    }

    fn start_controller(&mut self, interrupt_enable: bool) -> Result<(), PCIeDeviceErr> {
        let mut cmd =
            self.read_op(regs::op::USBCMD) | regs::op::CMD_RUN_STOP | regs::op::CMD_HSEE;
        if interrupt_enable {
            cmd |= regs::op::CMD_INTE;
        }
        self.write_op(regs::op::USBCMD, cmd);
        // HCHalted must deassert once the controller is running.
        if !self.poll_usbsts(regs::op::STS_HCH, 0, 1_000_000) {
            log::error!("xHCI: {}: controller did not start (HCH stuck set)", self.name);
            return Err(PCIeDeviceErr::InitFailure);
        }
        log::info!("xHCI: {}: controller running (INTE={})", self.name, interrupt_enable);
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Phase 3a: Port Status and Control register accessors
    // -------------------------------------------------------------------------

    /// Read PORTSC for 1-based port number `port`.
    pub fn read_portsc(&self, port: usize) -> u32 {
        self.read_op(regs::port::BASE + (port - 1) * regs::port::STRIDE)
    }

    /// Write PORTSC for 1-based port number `port`.
    pub fn write_portsc(&self, port: usize, val: u32) {
        self.write_op(regs::port::BASE + (port - 1) * regs::port::STRIDE, val)
    }

    // -------------------------------------------------------------------------
    // Phase 3a: Event Ring processing (call from ISR context or polling loop)
    // -------------------------------------------------------------------------

    /// Drain all pending events from the Event Ring and update ERDP after each one.
    /// Returns the number of events processed.
    pub fn process_events(&mut self) -> usize {
        let mut count = 0;
        loop {
            let trb = match self.evt_ring.dequeue() {
                Some(t) => t,
                None => break,
            };
            count += 1;

            let trb_type = (trb.ctrl >> regs::TRB_TYPE_SHIFT) & 0x3f;
            match trb_type {
                regs::trb_type::CMD_COMPLETION => self.on_cmd_completion(&trb),
                regs::trb_type::PORT_STATUS_CHANGE => self.on_port_status_change(&trb),
                regs::trb_type::TRANSFER_EVENT => self.on_transfer_event(&trb),
                t => log::debug!("xHCI: {}: unknown event type={}", self.name, t),
            }

            // Advance ERDP to the new dequeue position and clear Event Handler Busy.
            let erdp = self.evt_ring.dequeue_phys();
            self.write_ir0(regs::ir::ERDP_LO, erdp as u32 | regs::ir::ERDP_EHB);
            self.write_ir0(regs::ir::ERDP_HI, (erdp >> 32) as u32);
        }
        count
    }

    fn on_cmd_completion(&self, trb: &Trb) {
        let code = (trb.status >> 24) & 0xff;
        let slot = (trb.ctrl >> 24) as u8;
        log::info!("xHCI: {}: CMD_COMPLETION code={} slot={}", self.name, code, slot);
    }

    fn on_port_status_change(&mut self, trb: &Trb) {
        // Port ID (1-based) is in DWORD0 bits [31:24] of the event TRB param field.
        let port = (trb.param >> 24) as u8 as usize;
        if port == 0 || port > self.max_ports as usize {
            log::warn!("xHCI: {}: PSC event with invalid port {}", self.name, port);
            return;
        }

        let portsc = self.read_portsc(port);
        log::info!(
            "xHCI: {}: PORT_STATUS_CHANGE port={} PORTSC={:#010x}",
            self.name, port, portsc,
        );

        // Clear RW1CS change bits; avoid accidentally disabling the port (PED) or
        // re-triggering a port reset (PR).
        let write_val = (portsc & !(regs::port::PED | regs::port::PR))
            | (portsc & regs::port::CHANGE_BITS);
        self.write_portsc(port, write_val);

        if portsc & regs::port::CSC != 0 {
            if portsc & regs::port::CCS != 0 {
                // Device just connected — issue a port reset to start enumeration.
                log::info!("xHCI: {}: port {} connected, issuing port reset", self.name, port);
                let reset_val = (portsc & !(regs::port::PED | regs::port::CHANGE_BITS))
                    | regs::port::PR;
                self.write_portsc(port, reset_val);
            } else {
                log::info!("xHCI: {}: port {} disconnected", self.name, port);
            }
        }

        if portsc & regs::port::PRC != 0 {
            // Port reset completed — ready to issue Enable Slot command (Phase 3b).
            log::info!(
                "xHCI: {}: port {} reset complete, ready to enumerate",
                self.name, port,
            );
        }
    }

    fn on_transfer_event(&self, trb: &Trb) {
        let code = (trb.status >> 24) & 0xff;
        log::debug!("xHCI: {}: TRANSFER_EVENT code={}", self.name, code);
    }

    // -------------------------------------------------------------------------
    // Phase 3a: Command Ring submission helpers
    // -------------------------------------------------------------------------

    /// Enqueue a No-Op Command TRB and ring the command doorbell.
    /// Useful for verifying that the Command Ring is operational.
    pub fn send_noop_cmd(&mut self) {
        let trb = Trb {
            param: 0,
            status: 0,
            ctrl: regs::trb_type::NOOP_CMD << regs::TRB_TYPE_SHIFT,
        };
        if self.cmd_ring.enqueue(trb) {
            self.ring_cmd_doorbell();
            log::debug!("xHCI: {}: NOOP command enqueued", self.name);
        } else {
            log::warn!("xHCI: {}: command ring full, NOOP dropped", self.name);
        }
    }

    /// Enqueue an Enable Slot Command and ring the doorbell.
    /// The assigned slot ID is returned via a CMD_COMPLETION event (Phase 3b).
    pub fn send_enable_slot(&mut self) {
        let trb = Trb {
            param: 0,
            status: 0,
            ctrl: regs::trb_type::ENABLE_SLOT << regs::TRB_TYPE_SHIFT,
        };
        if self.cmd_ring.enqueue(trb) {
            self.ring_cmd_doorbell();
            log::info!("xHCI: {}: ENABLE_SLOT command enqueued", self.name);
        } else {
            log::warn!("xHCI: {}: command ring full, ENABLE_SLOT dropped", self.name);
        }
    }

    // -------------------------------------------------------------------------
    // Phase 3b: Synchronous polling helpers (boot-time, single-threaded)
    // -------------------------------------------------------------------------

    /// Poll PORTSC until `(portsc & mask) == expected`, up to `max_iter` times.
    fn poll_portsc(&self, port: usize, mask: u32, expected: u32, max_iter: u32) -> bool {
        for _ in 0..max_iter {
            if self.read_portsc(port) & mask == expected {
                return true;
            }
            core::hint::spin_loop();
        }
        false
    }

    /// Directly drain the Event Ring without any side-effects.
    /// Used to flush initial port-power-on events before the main enumeration loop.
    fn drain_events(&mut self) {
        loop {
            let trb = match self.evt_ring.dequeue() {
                Some(t) => t,
                None => break,
            };
            let t = (trb.ctrl >> regs::TRB_TYPE_SHIFT) & 0x3f;
            log::debug!("xHCI: {}: drain_events: type={}", self.name, t);
            let erdp = self.evt_ring.dequeue_phys();
            self.write_ir0(regs::ir::ERDP_LO, erdp as u32 | regs::ir::ERDP_EHB);
            self.write_ir0(regs::ir::ERDP_HI, (erdp >> 32) as u32);
        }
    }

    /// Poll the Event Ring until a CMD_COMPLETION TRB arrives.
    /// Returns `(completion_code, slot_id)`.
    fn poll_cmd_completion(&mut self, max_iter: u32) -> Option<(u8, u8)> {
        for _ in 0..max_iter {
            if let Some(trb) = self.evt_ring.dequeue() {
                let erdp = self.evt_ring.dequeue_phys();
                self.write_ir0(regs::ir::ERDP_LO, erdp as u32 | regs::ir::ERDP_EHB);
                self.write_ir0(regs::ir::ERDP_HI, (erdp >> 32) as u32);
                let trb_type = (trb.ctrl >> regs::TRB_TYPE_SHIFT) & 0x3f;
                if trb_type == regs::trb_type::CMD_COMPLETION {
                    return Some(((trb.status >> 24) as u8, (trb.ctrl >> 24) as u8));
                }
                // Skip non-CMD_COMPLETION events; they will be re-processed via
                // process_events() once the main loop runs.
            }
            core::hint::spin_loop();
        }
        None
    }

    /// Poll the Event Ring until a TRANSFER_EVENT TRB arrives.
    /// Returns the completion code.
    fn poll_xfer_completion(&mut self, max_iter: u32) -> Option<u8> {
        for _ in 0..max_iter {
            if let Some(trb) = self.evt_ring.dequeue() {
                let erdp = self.evt_ring.dequeue_phys();
                self.write_ir0(regs::ir::ERDP_LO, erdp as u32 | regs::ir::ERDP_EHB);
                self.write_ir0(regs::ir::ERDP_HI, (erdp >> 32) as u32);
                let trb_type = (trb.ctrl >> regs::TRB_TYPE_SHIFT) & 0x3f;
                if trb_type == regs::trb_type::TRANSFER_EVENT {
                    return Some((trb.status >> 24) as u8);
                }
            }
            core::hint::spin_loop();
        }
        None
    }

    /// Ring the doorbell for slot `slot` targeting endpoint `endpoint` (1 = EP0).
    fn write_slot_doorbell(&self, slot: u8, endpoint: u32) {
        unsafe { wr32(self.db_base, slot as usize * 4, endpoint) }
    }

    /// Enqueue an Address Device Command with the given Input Context physical address.
    /// `bsr=true` skips the SET_ADDRESS USB request (Block Set Address).
    fn send_address_device(&mut self, slot: u8, input_ctx_phys: u64, bsr: bool) {
        let bsr_bit: u32 = if bsr { 1 << 9 } else { 0 };
        let trb = Trb {
            param: input_ctx_phys,
            status: 0,
            ctrl: (regs::trb_type::ADDRESS_DEVICE << regs::TRB_TYPE_SHIFT)
                | bsr_bit
                | ((slot as u32) << 24),
        };
        if self.cmd_ring.enqueue(trb) {
            self.ring_cmd_doorbell();
        }
    }

    // -------------------------------------------------------------------------
    // Phase 3b: Device enumeration — Address Device + GET_DESCRIPTOR
    // -------------------------------------------------------------------------

    /// Complete device enumeration for a freshly-reset port.
    /// Sends Address Device, then retrieves the USB Device Descriptor.
    fn enumerate_port(&mut self, port: usize, slot: u8) -> Result<(), PCIeDeviceErr> {
        let ctx = self.ctx_size;
        log::info!("xHCI: {}: enumerating port={} slot={} ctx_size={}", self.name, port, slot, ctx);

        // Allocate a fresh Transfer Ring for EP0.
        let mut ep0_ring = TransferRing::new(0).ok_or(PCIeDeviceErr::InitFailure)?;
        ep0_ring.init();
        let ep0_phys = ep0_ring.phys_base();

        // Allocate Device Context (must persist; written to DCBAA[slot]).
        let mut dev_ctx = DMAPool::<[u8; 4096]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        for b in dev_ctx.as_mut().iter_mut() { *b = 0; }
        let dev_ctx_phys = dev_ctx.get_phy_addr().as_usize() as u64;
        self.dcbaa.mem.as_mut()[slot as usize] = dev_ctx_phys;

        // Allocate Input Context (transient; hardware only needs it during Address Device).
        let mut input_ctx = DMAPool::<[u8; 4096]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        let input_bytes = input_ctx.as_mut();
        for b in input_bytes.iter_mut() { *b = 0; }

        // Input Control Context: Add A0 (slot) + A1 (EP1 = EP0).
        ctx_write32(input_bytes, 0, 0);      // Drop flags = 0
        ctx_write32(input_bytes, 4, 0b11);   // Add A0 + A1

        // Slot Context (at offset ctx): Speed, ContextEntries=1, RootHubPort.
        let portsc = self.read_portsc(port);
        let speed = (portsc >> 10) & 0xf; // PORTSC bits [13:10]
        self.dev_speed = speed as u8;
        self.dev_port = port as u8;
        ctx_write32(input_bytes, ctx, (speed << 20) | (1 << 27)); // Speed, CtxEntries=1
        ctx_write32(input_bytes, ctx + 4, (port as u32) << 16);   // RootHubPort

        // EP1 (EP0) Context (at offset ctx*2): EPType=4, ErrorCount=3, MaxPacketSize, TR ptr.
        let ep0_ctx = ctx * 2;
        let max_pkt: u32 = match speed {
            3 => 64,       // High Speed
            4 | 5 => 512,  // SuperSpeed / SuperSpeed Plus
            _ => 8,        // Full Speed / Low Speed (safe initial value)
        };
        // DW1: ErrorCount[2:1]=3, EPType[5:3]=4 (Control), MaxPacketSize[31:16]
        ctx_write32(input_bytes, ep0_ctx + 4, (3 << 1) | (4 << 3) | (max_pkt << 16));
        // TR Dequeue Pointer (DCS=1 matches initial cycle_bit=1)
        ctx_write32(input_bytes, ep0_ctx + 8, ep0_phys as u32 | 1);
        ctx_write32(input_bytes, ep0_ctx + 12, (ep0_phys >> 32) as u32);
        // AvgTRBLen = 8 bytes (minimum for control endpoint)
        ctx_write32(input_bytes, ep0_ctx + 16, 8);

        let input_ctx_phys = input_ctx.get_phy_addr().as_usize() as u64;

        // Send Address Device (BSR=false → hardware sends SET_ADDRESS).
        self.send_address_device(slot, input_ctx_phys, false);
        let (code, _) = self.poll_cmd_completion(2_000_000)
            .ok_or(PCIeDeviceErr::InitFailure)?;
        if code != 1 {
            log::error!("xHCI: {}: Address Device failed (code={})", self.name, code);
            return Err(PCIeDeviceErr::InitFailure);
        }
        // input_ctx no longer needed after Address Device completes.
        drop(input_ctx);

        log::info!("xHCI: {}: slot {} addressed (USB addr assigned)", self.name, slot);

        // Persist EP0 ring and Device Context.
        self.ep0_ring = Some(ep0_ring);
        self.dev_ctx = Some(dev_ctx);
        self.dev_slot = Some(slot);

        // Retrieve Device Descriptor via GET_DESCRIPTOR control transfer.
        self.get_device_descriptor(slot)?;

        // Phase 4: attempt MSC bulk endpoint setup (silently skip if not MSC).
        if let Err(e) = self.try_setup_msc(slot) {
            log::warn!("xHCI: {}: MSC setup skipped: {:?}", self.name, e);
        }

        // Phase 6: attempt CDC-ACM setup only if MSC did not claim the bulk endpoints.
        if self.bulk_in_ring.is_none() {
            if let Err(e) = self.try_setup_cdcacm(slot) {
                log::warn!("xHCI: {}: CDC-ACM setup skipped: {:?}", self.name, e);
            }
        }

        // PL2303: attempt setup only if neither MSC nor CDC-ACM claimed the endpoints.
        if self.bulk_in_ring.is_none() {
            if let Err(e) = self.try_setup_pl2303(slot) {
                log::warn!("xHCI: {}: PL2303 setup skipped: {:?}", self.name, e);
            }
        }

        // Diagnostic: immediately write a test string via bulk OUT to confirm the
        // write path works before CDC_DEV_PTR is registered via the normal log mirror.
        if self.is_pl2303 || self.is_cdcacm {
            let _ = self.cdcacm_write(slot, b"\r\n[awkernel USB diag OK]\r\n");
        }
        Ok(())
    }

    /// Issue a GET_DESCRIPTOR(Device) control transfer on EP0 and log the result.
    fn get_device_descriptor(&mut self, slot: u8) -> Result<(), PCIeDeviceErr> {
        // Allocate a 64-byte DMA buffer for the incoming descriptor.
        let mut desc_buf = DMAPool::<[u8; 64]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        for b in desc_buf.as_mut().iter_mut() { *b = 0; }
        let desc_phys = desc_buf.get_phy_addr().as_usize() as u64;

        let ep0_ring = self.ep0_ring.as_mut().ok_or(PCIeDeviceErr::InitFailure)?;

        // Setup Stage TRB: GET_DESCRIPTOR(Device), wLength=18, IDT=1, TRT=3 (IN).
        ep0_ring.enqueue(Trb {
            param: (0x80u64)         // bmRequestType = 0x80 (D→H, Std, Device)
                | (6u64 << 8)        // bRequest = GET_DESCRIPTOR
                | (0x0100u64 << 16)  // wValue   = 0x0100 (Device Descriptor)
                | (0u64 << 32)       // wIndex   = 0
                | (18u64 << 48),     // wLength  = 18
            status: 8,               // TRB Transfer Length = 8 (setup packet size)
            ctrl: (regs::trb_type::SETUP_STAGE << regs::TRB_TYPE_SHIFT)
                | (1 << 6)           // IDT = 1 (setup packet in param)
                | (3 << 16),         // TRT = 3 (IN Data Stage follows)
        });

        // Data Stage TRB: receive 18 bytes into desc_buf. DIR=1 (IN). No IOC here.
        ep0_ring.enqueue(Trb {
            param: desc_phys,
            status: 18,
            ctrl: (regs::trb_type::DATA_STAGE << regs::TRB_TYPE_SHIFT)
                | (1 << 16),         // DIR = 1 (IN)
        });

        // Status Stage TRB: OUT direction (opposite of IN data stage). IOC=1.
        ep0_ring.enqueue(Trb {
            param: 0,
            status: 0,
            ctrl: (regs::trb_type::STATUS_STAGE << regs::TRB_TYPE_SHIFT)
                | (1 << 5),          // IOC = 1
                                     // DIR = 0 (OUT status for an IN data stage)
        });

        // Ring EP0 doorbell: endpoint_id=1 (EP0 / default control pipe).
        self.write_slot_doorbell(slot, 1);

        // Wait for the Status Stage TRANSFER_EVENT (completion code 1 = Success).
        // Two TRANSFER_EVENTs may arrive (Data + Status); we accept the first Success.
        for _ in 0..2 {
            let code = self.poll_xfer_completion(2_000_000)
                .ok_or(PCIeDeviceErr::InitFailure)?;
            // code 1=Success, 13=Short Packet (also acceptable for GET_DESCRIPTOR).
            if code == 1 || code == 13 {
                break;
            }
            if code != 1 && code != 13 {
                log::error!("xHCI: {}: GET_DESCRIPTOR transfer error (code={})", self.name, code);
                return Err(PCIeDeviceErr::InitFailure);
            }
        }

        // Parse the Device Descriptor (18 bytes, §9.6.1 of USB 3.2 spec).
        let d = desc_buf.as_mut();
        let bcd_usb    = u16::from_le_bytes([d[2], d[3]]);
        let dev_class  = d[4];
        let dev_sub    = d[5];
        let dev_proto  = d[6];
        let max_pkt0   = d[7];
        let id_vendor  = u16::from_le_bytes([d[8], d[9]]);
        let id_product = u16::from_le_bytes([d[10], d[11]]);
        let bcd_dev    = u16::from_le_bytes([d[12], d[13]]);

        // Cache fields needed by try_setup_pl2303() later.
        self.dev_vid      = id_vendor;
        self.dev_pid      = id_product;
        self.dev_bcd      = bcd_dev;
        self.dev_class    = dev_class;
        self.dev_max_pkt0 = max_pkt0;

        log::info!(
            "xHCI: {}: slot {} — USB {}.{:02} VID={:#06x} PID={:#06x} \
             class={:#04x}/{:#04x}/{:#04x} bcdDevice={:#06x}",
            self.name, slot,
            bcd_usb >> 8, bcd_usb & 0xff,
            id_vendor, id_product,
            dev_class, dev_sub, dev_proto,
            bcd_dev,
        );

        if dev_class == 0x00 && dev_sub == 0x00 {
            log::info!("xHCI: {}: slot {} — class defined per interface (check config desc)", self.name, slot);
        }
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Phase 3b: Boot-time enumeration (called synchronously from attach())
    // -------------------------------------------------------------------------

    /// Scan all ports for a CDC-ACM or PL2303 device and enumerate the first match.
    /// Tries every port with CCS=1 in order; stops as soon as a serial adapter is found.
    pub fn boot_enumerate(&mut self) {
        // Ensure port power (PP) is on before waiting for device connection.
        // xHCI §4.19.1.1: if PPC=1 (power-controller present), software must set PP=1.
        // Writing PR=1 on an unpowered port (PP=0) is silently ignored by hardware.
        for p in 1..=self.max_ports as usize {
            let portsc = self.read_portsc(p);
            if portsc & regs::port::PP == 0 {
                // Set PP=1; preserve RWS bits; clear any stale change bits (RW1CS).
                self.write_portsc(
                    p,
                    (portsc & !(regs::port::PED | regs::port::PR))
                        | (portsc & regs::port::CHANGE_BITS)
                        | regs::port::PP,
                );
                log::info!("xHCI: {}: port {} PP was 0, powered on", self.name, p);
            }
        }

        // Test command ring with a NOOP before touching any port.
        // If NOOP times out, all Enable Slot attempts will also fail — report early.
        self.send_noop_cmd();
        match self.poll_cmd_completion(2_000_000) {
            Some((code, _)) if code == 1 => {
                XHCI_NOOP_RESULT.store(1, Ordering::Relaxed);
                log::info!("xHCI: {}: NOOP command OK — command ring is alive", self.name);
            }
            Some((code, _)) => {
                XHCI_NOOP_RESULT.store(2, Ordering::Relaxed);
                let usbsts = self.read_op(regs::op::USBSTS);
                XHCI_USBSTS_ON_SLOT_FAIL.store(usbsts, Ordering::Relaxed);
                log::warn!("xHCI: {}: NOOP failed (code={}) USBSTS={:#010x}", self.name, code, usbsts);
                return;
            }
            None => {
                XHCI_NOOP_RESULT.store(2, Ordering::Relaxed);
                let usbsts = self.read_op(regs::op::USBSTS);
                XHCI_USBSTS_ON_SLOT_FAIL.store(usbsts, Ordering::Relaxed);
                log::error!(
                    "xHCI: {}: NOOP timeout — command ring dead. USBSTS={:#010x}",
                    self.name, usbsts,
                );
                return; // No point resetting ports if commands don't complete.
            }
        }

        // Wait up to ~500ms for VBUS stabilization and device connection.
        awkernel_lib::delay::wait_microsec(500_000);
        self.drain_events();

        // Collect all ports that report a device connected.
        let mut ccs_ports: alloc::vec::Vec<usize> = alloc::vec::Vec::new();
        for p in 1..=self.max_ports as usize {
            if self.read_portsc(p) & regs::port::CCS != 0 {
                ccs_ports.push(p);
            }
        }

        XHCI_CCS_SEEN.fetch_add(ccs_ports.len(), Ordering::Relaxed);

        if ccs_ports.is_empty() {
            log::info!("xHCI: {}: no device found at boot", self.name);
            return;
        }

        for port in ccs_ports {
            log::info!("xHCI: {}: device detected on port {}", self.name, port);

            // Issue port reset and wait for PRC (Port Reset Change).
            // RW1CS rule: to clear change bits write 1; writing 0 has no effect.
            // Pre-clear any stale change bits while setting PR; keep PP, avoid PED.
            let portsc = self.read_portsc(port);
            self.write_portsc(
                port,
                (portsc & !regs::port::PED)
                    | (portsc & regs::port::CHANGE_BITS)
                    | regs::port::PR,
            );
            if !self.poll_portsc(port, regs::port::PRC, regs::port::PRC, 2_000_000) {
                log::error!("xHCI: {}: port {} reset timeout", self.name, port);
                continue;
            }
            XHCI_PORT_RESET_OK.fetch_add(1, Ordering::Relaxed);
            // Clear PRC (and any other change bits) by writing 1 to them (RW1CS).
            let portsc = self.read_portsc(port);
            self.write_portsc(
                port,
                (portsc & !(regs::port::PED | regs::port::PR))
                    | (portsc & regs::port::CHANGE_BITS),
            );
            self.drain_events();

            // Enable Slot — each port attempt gets its own slot number.
            self.send_enable_slot();
            let (code, slot) = match self.poll_cmd_completion(2_000_000) {
                Some(r) => r,
                None => {
                    let usbsts = self.read_op(regs::op::USBSTS);
                    XHCI_USBSTS_ON_SLOT_FAIL.store(usbsts, Ordering::Relaxed);
                    log::error!(
                        "xHCI: {}: Enable Slot timeout port={} USBSTS={:#010x}",
                        self.name, port, usbsts,
                    );
                    continue;
                }
            };
            if code != 1 {
                log::error!("xHCI: {}: Enable Slot failed (code={}) on port {}", self.name, code, port);
                continue;
            }
            XHCI_SLOT_ENABLED.fetch_add(1, Ordering::Relaxed);
            log::info!("xHCI: {}: slot {} assigned for port {}", self.name, slot, port);

            if let Err(e) = self.enumerate_port(port, slot) {
                log::error!("xHCI: {}: port {} enumerate_port failed: {:?}", self.name, port, e);
                self.abandon_dev_state();
                continue;
            }
            XHCI_ENUM_OK.fetch_add(1, Ordering::Relaxed);

            if self.is_pl2303 || self.is_cdcacm {
                return; // Found our serial adapter — done.
            }

            // Device found but not a serial adapter; leak its DMA state (hardware still
            // holds a reference through DCBAA) and try the next port.
            self.abandon_dev_state();
        }
    }

    /// Discard per-device state after enumerating a non-serial device.
    /// DMA allocations are intentionally leaked — the xHCI controller retains a
    /// reference through the DCBAA and the slot cannot be safely disabled here.
    fn abandon_dev_state(&mut self) {
        if let Some(ctx)  = self.dev_ctx.take()        { core::mem::forget(ctx); }
        if let Some(r)    = self.ep0_ring.take()        { core::mem::forget(r); }
        if let Some(r)    = self.bulk_in_ring.take()    { core::mem::forget(r); }
        if let Some(r)    = self.bulk_out_ring.take()   { core::mem::forget(r); }
        if let Some(dma)  = self.cdcacm_tx_dma.take()  { core::mem::forget(dma); }
        self.dev_slot       = None;
        self.is_pl2303      = false;
        self.is_cdcacm      = false;
        self.dev_vid        = 0;
        self.dev_pid        = 0;
        self.dev_bcd        = 0;
        self.dev_class      = 0;
        self.dev_max_pkt0   = 0;
        self.dev_speed      = 0;
        self.dev_port       = 0;
        self.cdcacm_ctrl_if = 0;
        self.cdcacm_max_pkt = 0;
        self.bulk_in_ep_id  = 0;
        self.bulk_out_ep_id = 0;
    }
    // -------------------------------------------------------------------------
    // Phase 4a: Generic control transfer helpers
    // -------------------------------------------------------------------------

    /// IN control transfer: Setup(TRT=3) + Data(DIR=IN) + Status(DIR=OUT, IOC).
    fn control_transfer_in(
        &mut self, slot: u8,
        setup_param: u64, data_phys: u64, data_len: usize,
    ) -> Result<(), PCIeDeviceErr> {
        {
            let r = self.ep0_ring.as_mut().ok_or(PCIeDeviceErr::InitFailure)?;
            r.enqueue(Trb {
                param: setup_param,
                status: 8,
                ctrl: (regs::trb_type::SETUP_STAGE << regs::TRB_TYPE_SHIFT)
                    | (1 << 6)   // IDT
                    | (3 << 16), // TRT=3 (IN data stage)
            });
            r.enqueue(Trb {
                param: data_phys,
                status: data_len as u32,
                ctrl: (regs::trb_type::DATA_STAGE << regs::TRB_TYPE_SHIFT)
                    | (1 << 16), // DIR=IN
            });
            r.enqueue(Trb {
                param: 0,
                status: 0,
                ctrl: (regs::trb_type::STATUS_STAGE << regs::TRB_TYPE_SHIFT)
                    | (1 << 5), // IOC; DIR=OUT (0) for an IN transfer
            });
        }
        self.write_slot_doorbell(slot, 1);
        // Accept up to two TRANSFER_EVENTs (Data + Status may both fire with IOC).
        for _ in 0..2 {
            let code = self.poll_xfer_completion(2_000_000)
                .ok_or(PCIeDeviceErr::InitFailure)?;
            if code == 1 || code == 13 {
                return Ok(());
            }
            log::error!("xHCI: control_transfer_in: code={}", code);
            return Err(PCIeDeviceErr::InitFailure);
        }
        Ok(())
    }

    /// OUT control transfer with no data stage: Setup(TRT=0) + Status(DIR=IN, IOC).
    fn control_transfer_out(
        &mut self, slot: u8, setup_param: u64,
    ) -> Result<(), PCIeDeviceErr> {
        {
            let r = self.ep0_ring.as_mut().ok_or(PCIeDeviceErr::InitFailure)?;
            r.enqueue(Trb {
                param: setup_param,
                status: 8,
                ctrl: (regs::trb_type::SETUP_STAGE << regs::TRB_TYPE_SHIFT)
                    | (1 << 6), // IDT; TRT=0 (no data stage)
            });
            r.enqueue(Trb {
                param: 0,
                status: 0,
                ctrl: (regs::trb_type::STATUS_STAGE << regs::TRB_TYPE_SHIFT)
                    | (1 << 16) // DIR=IN (status for an OUT-type control transfer)
                    | (1 << 5), // IOC
            });
        }
        self.write_slot_doorbell(slot, 1);
        let code = self.poll_xfer_completion(2_000_000)
            .ok_or(PCIeDeviceErr::InitFailure)?;
        if code != 1 {
            log::error!("xHCI: control_transfer_out: code={}", code);
            return Err(PCIeDeviceErr::InitFailure);
        }
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Phase 7: OUT control transfer with data stage (used by SET_LINE_CODING)
    // -------------------------------------------------------------------------

    /// OUT control transfer WITH an outbound data stage.
    /// Flow: Setup(TRT=2) → Data Stage(DIR=OUT) → Status Stage(DIR=IN, IOC).
    fn control_transfer_out_with_data(
        &mut self, slot: u8, setup_param: u64, data_phys: u64, data_len: usize,
    ) -> Result<(), PCIeDeviceErr> {
        {
            let r = self.ep0_ring.as_mut().ok_or(PCIeDeviceErr::InitFailure)?;
            r.enqueue(Trb {
                param: setup_param,
                status: 8,
                ctrl: (regs::trb_type::SETUP_STAGE << regs::TRB_TYPE_SHIFT)
                    | (1 << 6)   // IDT = 1 (setup packet in param)
                    | (2 << 16), // TRT = 2 (OUT data stage follows)
            });
            r.enqueue(Trb {
                param: data_phys,
                status: data_len as u32,
                ctrl: regs::trb_type::DATA_STAGE << regs::TRB_TYPE_SHIFT,
                // DIR = 0 (OUT); no IOC here
            });
            r.enqueue(Trb {
                param: 0,
                status: 0,
                ctrl: (regs::trb_type::STATUS_STAGE << regs::TRB_TYPE_SHIFT)
                    | (1 << 16) // DIR = 1 (IN status for an OUT-data transfer)
                    | (1 << 5), // IOC
            });
        }
        self.write_slot_doorbell(slot, 1);
        for _ in 0..2 {
            let code = self.poll_xfer_completion(2_000_000)
                .ok_or(PCIeDeviceErr::InitFailure)?;
            if code == 1 || code == 13 {
                return Ok(());
            }
            log::error!("xHCI: control_transfer_out_with_data: code={}", code);
            return Err(PCIeDeviceErr::InitFailure);
        }
        Ok(())
    }

    /// CDC SET_LINE_CODING (bRequest=0x20) — send a 7-byte Line Coding structure.
    ///
    /// `baud`      — DTE baud rate in bits/second (e.g. 115200)
    /// `stop_bits` — 0 = 1 stop bit, 1 = 1.5 stop bits, 2 = 2 stop bits
    /// `parity`    — 0 = None, 1 = Odd, 2 = Even, 3 = Mark, 4 = Space
    /// `data_bits` — 5 / 6 / 7 / 8 / 16
    fn cdcacm_set_line_coding(
        &mut self, slot: u8, ctrl_if: u8,
        baud: u32, stop_bits: u8, parity: u8, data_bits: u8,
    ) -> Result<(), PCIeDeviceErr> {
        let mut buf = DMAPool::<[u8; 16]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        {
            let b = buf.as_mut();
            for x in b.iter_mut() { *x = 0; }
            b[0..4].copy_from_slice(&baud.to_le_bytes());
            b[4] = stop_bits;
            b[5] = parity;
            b[6] = data_bits;
        }
        let phys = buf.get_phy_addr().as_usize() as u64;

        // bmRequestType=0x21 (OUT, Class, Interface)  bRequest=0x20 (SET_LINE_CODING)
        // wValue=0  wIndex=ctrl_if  wLength=7
        let setup: u64 = 0x21u64
            | (0x20u64 << 8)
            | (0u64    << 16)
            | ((ctrl_if as u64) << 32)
            | (7u64    << 48);

        self.control_transfer_out_with_data(slot, setup, phys, 7)
    }

    /// CDC SET_CONTROL_LINE_STATE (bRequest=0x22) — assert DTR and/or RTS.
    ///
    /// wValue bit 0 = DTR, bit 1 = RTS.  No data stage.
    fn cdcacm_set_control_line_state(
        &mut self, slot: u8, ctrl_if: u8, dtr: bool, rts: bool,
    ) -> Result<(), PCIeDeviceErr> {
        let wvalue: u64 = (if dtr { 1 } else { 0 }) | (if rts { 2 } else { 0 });
        // bmRequestType=0x21 (OUT, Class, Interface)  bRequest=0x22 (SET_CONTROL_LINE_STATE)
        // wValue=DTR|RTS  wIndex=ctrl_if  wLength=0
        let setup: u64 = 0x21u64
            | (0x22u64 << 8)
            | (wvalue  << 16)
            | ((ctrl_if as u64) << 32)
            | (0u64    << 48);

        self.control_transfer_out(slot, setup)
    }

    // -------------------------------------------------------------------------
    // PL2303: vendor control transfer helpers (bRequest = 0x01)
    // -------------------------------------------------------------------------

    /// Vendor-specific IN transfer: read 1 byte from the PL2303 register at `wvalue`.
    /// The byte is discarded; we only care whether the transfer succeeds.
    fn pl2303_vendor_read(&mut self, slot: u8, wvalue: u16, windex: u16)
        -> Result<(), PCIeDeviceErr>
    {
        let mut buf = DMAPool::<[u8; 4]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        for b in buf.as_mut().iter_mut() { *b = 0; }
        let phys = buf.get_phy_addr().as_usize() as u64;
        // bmRequestType=0xC0 (IN, Vendor, Device)  bRequest=0x01  wLength=1
        let setup: u64 = 0xC0u64
            | (0x01u64 << 8)
            | ((wvalue as u64) << 16)
            | ((windex as u64) << 32)
            | (1u64 << 48);
        self.control_transfer_in(slot, setup, phys, 1)
    }

    /// Vendor-specific OUT transfer with no data stage: write to PL2303 register.
    /// bmRequestType=0x40 (OUT, Vendor, Device), bRequest=0x01, wLength=0.
    fn pl2303_vendor_write(&mut self, slot: u8, wvalue: u16, windex: u16)
        -> Result<(), PCIeDeviceErr>
    {
        let setup: u64 = 0x40u64
            | (0x01u64 << 8)
            | ((wvalue as u64) << 16)
            | ((windex as u64) << 32)
            | (0u64 << 48);
        self.control_transfer_out(slot, setup)
    }

    // -------------------------------------------------------------------------
    // PL2303: initialization sequence (uplcom_pl2303_init from FreeBSD uplcom.c)
    // -------------------------------------------------------------------------

    /// Run the chip-type-specific initialization sequence.
    ///
    /// Sequence reference: FreeBSD sys/dev/usb/serial/uplcom.c `uplcom_pl2303_init()`
    /// and the surrounding code in `uplcom_attach()`.
    fn pl2303_init_seq(
        &mut self, slot: u8, chip_type: pl2303::ChipType, data_iface_no: u8,
    ) -> Result<(), PCIeDeviceErr> {
        use pl2303::ChipType;

        if chip_type == ChipType::Hxn {
            // HXN uses a completely different command set (bRequest=0x80).
            // A single pre-init write is all that is required before SET_LINE_CODING.
            let setup: u64 = 0x40u64
                | (0x80u64 << 8)   // UPLCOM_SET_REQUEST_PL2303HXN
                | (0x07u64 << 16)  // wValue = 0x07
                | (0x03u64 << 32)  // wIndex = 0x03
                | (0u64 << 48);
            let _ = self.control_transfer_out(slot, setup);
            return Ok(());
        }

        // HX / HXD: pipe-reset writes before the main reset.
        if chip_type == ChipType::Hx || chip_type == ChipType::Hxd {
            let _ = self.pl2303_vendor_write(slot, 8, 0); // wValue=8, wIndex=0
            let _ = self.pl2303_vendor_write(slot, 9, 0); // wValue=9, wIndex=0
        }

        // Reset: wValue=0, wIndex=data_iface_no  (uplcom_reset in FreeBSD)
        let _ = self.pl2303_vendor_write(slot, 0x0000, data_iface_no as u16);

        // 10-step common init sequence (uplcom_pl2303_init, steps 1-10).
        // Reads are fire-and-forget; the returned byte is not used.
        self.pl2303_vendor_read(slot,  0x8484, 0)?;
        self.pl2303_vendor_write(slot, 0x0404, 0)?;
        self.pl2303_vendor_read(slot,  0x8484, 0)?;
        self.pl2303_vendor_read(slot,  0x8383, 0)?;
        self.pl2303_vendor_read(slot,  0x8484, 0)?;
        self.pl2303_vendor_write(slot, 0x0404, 1)?;
        self.pl2303_vendor_read(slot,  0x8484, 0)?;
        self.pl2303_vendor_read(slot,  0x8383, 0)?;
        self.pl2303_vendor_write(slot, 0x0000, 1)?; // wValue=0x0000, wIndex=0x0001
        self.pl2303_vendor_write(slot, 0x0001, 0)?; // wValue=0x0001, wIndex=0x0000

        // Step 11: mode byte — 0x24 for original PL2303, 0x44 for HX/HXD.
        let mode_windex: u16 = match chip_type {
            ChipType::Original => 0x24,
            _                  => 0x44,
        };
        self.pl2303_vendor_write(slot, 0x0002, mode_windex)?;

        Ok(())
    }

    // -------------------------------------------------------------------------
    // PL2303: top-level detection and setup
    // -------------------------------------------------------------------------

    /// Detect a PL2303 USB-to-RS232 adapter, run its initialization sequence,
    /// and configure 115200 8N1 with DTR + RTS asserted.
    ///
    /// Reuses the existing CDC-ACM TX infrastructure (`cdcacm_write`, `cdcacm_tx_dma`)
    /// since both devices use standard USB bulk OUT for serial data.
    fn try_setup_pl2303(&mut self, slot: u8) -> Result<(), PCIeDeviceErr> {
        if !pl2303::is_pl2303(self.dev_vid, self.dev_pid) {
            return Ok(());
        }
        XHCI_PL2303_VID_SEEN.store(true, Ordering::Relaxed);

        log::info!(
            "xHCI: {}: slot {} — PL2303 detected VID={:#06x} PID={:#06x} bcdDevice={:#06x}",
            self.name, slot, self.dev_vid, self.dev_pid, self.dev_bcd,
        );

        // Walk the configuration descriptor for bulk endpoints.
        let (cfg, cfg_len) = self.get_config_descriptor(slot)?;
        XHCI_PL2303_GOT_CFG.store(true, Ordering::Relaxed);

        let mut info = match pl2303::find_bulk_endpoints(&cfg, cfg_len) {
            Some(i) => i,
            None => {
                log::error!("xHCI: {}: slot {} — PL2303 bulk endpoints not found", self.name, slot);
                return Err(PCIeDeviceErr::InitFailure);
            }
        };
        XHCI_PL2303_GOT_EPS.store(true, Ordering::Relaxed);

        // Determine chip type from cached device descriptor fields.
        let mut chip_type = pl2303::detect_chip_type(
            self.dev_bcd, self.dev_class, self.dev_max_pkt0,
        );

        // Distinguish HX from HXN: reading register 0x8080 fails on HXN.
        if chip_type == pl2303::ChipType::Hx {
            if self.pl2303_vendor_read(slot, 0x8080, info.data_iface_no as u16).is_err() {
                chip_type = pl2303::ChipType::Hxn;
                log::info!("xHCI: {}: slot {} — PL2303HXN confirmed", self.name, slot);
            }
        }
        info.chip_type = chip_type;

        log::info!(
            "xHCI: {}: slot {} — PL2303 {:?} iface={} IN={:#04x} OUT={:#04x} max_pkt={}",
            self.name, slot, chip_type, info.data_iface_no,
            info.bulk_in_addr, info.bulk_out_addr, info.max_pkt,
        );

        self.set_configuration(slot, info.config_val)?;
        XHCI_PL2303_SET_CFG.store(true, Ordering::Relaxed);

        self.configure_bulk_endpoints(
            slot, info.bulk_in_addr, info.bulk_out_addr, info.max_pkt,
        )?;
        XHCI_PL2303_CFG_EPS.store(true, Ordering::Relaxed);

        // Phase B: chip initialization sequence.
        self.pl2303_init_seq(slot, chip_type, info.data_iface_no)?;
        XHCI_PL2303_INIT_SEQ.store(true, Ordering::Relaxed);

        // SET_LINE_CODING (115200 8N1) — same CDC class request as CDC-ACM,
        // but wIndex = data_iface_no (PL2303 uses the data interface for class requests).
        self.cdcacm_set_line_coding(slot, info.data_iface_no, 115_200, 0, 0, 8)?;

        // SET_CONTROL_LINE_STATE (DTR=1, RTS=1).
        self.cdcacm_set_control_line_state(slot, info.data_iface_no, true, true)?;

        self.is_pl2303    = true;
        self.cdcacm_max_pkt = info.max_pkt;

        // Phase C: pre-allocate the DMA TX buffer (shared with CDC-ACM path).
        if self.cdcacm_tx_dma.is_none() {
            let mut tx = DMAPool::<[u8; 512]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
            for b in tx.as_mut().iter_mut() { *b = 0; }
            self.cdcacm_tx_dma = Some(tx);
        }

        log::info!(
            "xHCI: {}: slot {} — PL2303 ready for TX (115200 8N1 DTR+RTS)",
            self.name, slot,
        );
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Phase 4a: Configuration descriptor + endpoint discovery
    // -------------------------------------------------------------------------

    /// GET_DESCRIPTOR(Configuration): fetch up to 255 bytes, return (buf, total_len).
    fn get_config_descriptor(&mut self, slot: u8) -> Result<([u8; 255], usize), PCIeDeviceErr> {
        let mut buf = DMAPool::<[u8; 256]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        for b in buf.as_mut().iter_mut() { *b = 0; }
        let phys = buf.get_phy_addr().as_usize() as u64;

        // First pass: 9 bytes to learn wTotalLength.
        let setup9: u64 = 0x80u64 | (6u64 << 8) | (0x0200u64 << 16) | (9u64 << 48);
        self.control_transfer_in(slot, setup9, phys, 9)?;

        let total = u16::from_le_bytes([buf.as_mut()[2], buf.as_mut()[3]]) as usize;
        let fetch = total.min(255);

        // Second pass: full descriptor.
        for b in buf.as_mut().iter_mut() { *b = 0; }
        let setup_full: u64 =
            0x80u64 | (6u64 << 8) | (0x0200u64 << 16) | ((fetch as u64) << 48);
        self.control_transfer_in(slot, setup_full, phys, fetch)?;

        let mut out = [0u8; 255];
        out[..fetch].copy_from_slice(&buf.as_mut()[..fetch]);
        Ok((out, fetch))
    }

    /// SET_CONFIGURATION(config_val) — no data stage.
    fn set_configuration(&mut self, slot: u8, config_val: u8) -> Result<(), PCIeDeviceErr> {
        let setup: u64 = 0x00u64              // bmRequestType=0x00 (OUT, Std, Device)
            | (9u64 << 8)                      // bRequest=SET_CONFIGURATION
            | ((config_val as u64) << 16);     // wValue=config_val, wIndex=0, wLength=0
        self.control_transfer_out(slot, setup)
    }

    // -------------------------------------------------------------------------
    // Phase 8: CDC-ACM bulk OUT write
    // -------------------------------------------------------------------------

    /// Write `data` bytes to the CDC-ACM bulk OUT endpoint in max_pkt-sized chunks.
    /// Uses the pre-allocated `cdcacm_tx_dma` buffer; must be called after
    /// `try_setup_cdcacm()` has succeeded.
    fn cdcacm_write(&mut self, slot: u8, data: &[u8]) -> Result<(), PCIeDeviceErr> {
        let max_pkt = (self.cdcacm_max_pkt as usize).min(512).max(1);

        let tx_phys = self.cdcacm_tx_dma
            .as_ref()
            .ok_or(PCIeDeviceErr::InitFailure)?
            .get_phy_addr().as_usize() as u64;

        for chunk in data.chunks(max_pkt) {
            {
                let tx = self.cdcacm_tx_dma.as_mut()
                    .ok_or(PCIeDeviceErr::InitFailure)?;
                let b = tx.as_mut();
                b[..chunk.len()].copy_from_slice(chunk);
            }
            self.bulk_out_transfer(slot, tx_phys, chunk.len() as u32)?;
        }
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Phase 4b: CONFIGURE_EP + bulk Transfer Ring setup
    // -------------------------------------------------------------------------

    /// Issue CONFIGURE_EP to add bulk IN and OUT endpoints, then allocate their rings.
    fn configure_bulk_endpoints(
        &mut self, slot: u8,
        bulk_in_addr: u8, bulk_out_addr: u8, max_pkt: u16,
    ) -> Result<(), PCIeDeviceErr> {
        // xHCI DCI: IN = ep_num*2+1,  OUT = ep_num*2  (ep_num ≥ 1).
        let in_dci = ((bulk_in_addr & 0xf) as usize) * 2 + 1;
        let out_dci = ((bulk_out_addr & 0xf) as usize) * 2;
        let max_dci = in_dci.max(out_dci);

        let mut in_ring = TransferRing::new(0).ok_or(PCIeDeviceErr::InitFailure)?;
        in_ring.init();
        let in_phys = in_ring.phys_base();

        let mut out_ring = TransferRing::new(0).ok_or(PCIeDeviceErr::InitFailure)?;
        out_ring.init();
        let out_phys = out_ring.phys_base();

        let ctx = self.ctx_size;
        let speed = self.dev_speed as u32;
        let port = self.dev_port as u32;

        let mut input_ctx = DMAPool::<[u8; 4096]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        {
            let b = input_ctx.as_mut();
            for x in b.iter_mut() { *x = 0; }

            // Input Control Context: add Slot (bit 0) + bulk IN (bit in_dci) + bulk OUT (bit out_dci).
            let add: u32 = (1 << 0) | (1u32 << in_dci) | (1u32 << out_dci);
            ctx_write32(b, 0, 0);   // Drop flags = 0
            ctx_write32(b, 4, add); // Add flags

            // Slot Context: update ContextEntries to max_dci.
            ctx_write32(b, ctx, (speed << 20) | ((max_dci as u32) << 27));
            ctx_write32(b, ctx + 4, port << 16);

            // Bulk IN EP Context (EPType=6).
            let in_off = ctx * (in_dci + 1);
            ctx_write32(b, in_off + 4, (3 << 1) | (6 << 3) | ((max_pkt as u32) << 16));
            ctx_write32(b, in_off + 8, in_phys as u32 | 1); // DCS=1
            ctx_write32(b, in_off + 12, (in_phys >> 32) as u32);
            ctx_write32(b, in_off + 16, max_pkt as u32); // AvgTRBLen

            // Bulk OUT EP Context (EPType=2).
            let out_off = ctx * (out_dci + 1);
            ctx_write32(b, out_off + 4, (3 << 1) | (2 << 3) | ((max_pkt as u32) << 16));
            ctx_write32(b, out_off + 8, out_phys as u32 | 1);
            ctx_write32(b, out_off + 12, (out_phys >> 32) as u32);
            ctx_write32(b, out_off + 16, max_pkt as u32);
        }
        let input_phys = input_ctx.get_phy_addr().as_usize() as u64;

        let trb = Trb {
            param: input_phys,
            status: 0,
            ctrl: (regs::trb_type::CONFIGURE_EP << regs::TRB_TYPE_SHIFT)
                | ((slot as u32) << 24),
        };
        if self.cmd_ring.enqueue(trb) {
            self.ring_cmd_doorbell();
        }
        drop(input_ctx);

        let (code, _) = self.poll_cmd_completion(2_000_000)
            .ok_or(PCIeDeviceErr::InitFailure)?;
        if code != 1 {
            log::error!("xHCI: {}: CONFIGURE_EP failed (code={})", self.name, code);
            return Err(PCIeDeviceErr::InitFailure);
        }

        self.bulk_in_ring = Some(in_ring);
        self.bulk_out_ring = Some(out_ring);
        self.bulk_in_ep_id = in_dci as u8;
        self.bulk_out_ep_id = out_dci as u8;

        log::info!(
            "xHCI: {}: slot {} bulk EPs configured: IN_DCI={} OUT_DCI={} max_pkt={}",
            self.name, slot, in_dci, out_dci, max_pkt,
        );
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Phase 4b: Bulk transfer primitives
    // -------------------------------------------------------------------------

    /// Enqueue one Normal TRB on the bulk OUT ring and wait for TRANSFER_EVENT.
    fn bulk_out_transfer(
        &mut self, slot: u8, buf_phys: u64, len: u32,
    ) -> Result<(), PCIeDeviceErr> {
        let ep_id = self.bulk_out_ep_id as u32;
        {
            let r = self.bulk_out_ring.as_mut().ok_or(PCIeDeviceErr::InitFailure)?;
            r.enqueue(Trb {
                param: buf_phys,
                status: len,
                ctrl: (regs::trb_type::NORMAL << regs::TRB_TYPE_SHIFT) | (1 << 5), // IOC
            });
        }
        self.write_slot_doorbell(slot, ep_id);
        let code = self.poll_xfer_completion(2_000_000)
            .ok_or(PCIeDeviceErr::InitFailure)?;
        if code != 1 && code != 13 {
            log::error!("xHCI: bulk OUT failed (code={})", code);
            return Err(PCIeDeviceErr::InitFailure);
        }
        Ok(())
    }

    /// Enqueue one Normal TRB on the bulk IN ring and wait for TRANSFER_EVENT.
    fn bulk_in_transfer(
        &mut self, slot: u8, buf_phys: u64, len: u32,
    ) -> Result<(), PCIeDeviceErr> {
        let ep_id = self.bulk_in_ep_id as u32;
        {
            let r = self.bulk_in_ring.as_mut().ok_or(PCIeDeviceErr::InitFailure)?;
            r.enqueue(Trb {
                param: buf_phys,
                status: len,
                ctrl: (regs::trb_type::NORMAL << regs::TRB_TYPE_SHIFT) | (1 << 5), // IOC
            });
        }
        self.write_slot_doorbell(slot, ep_id);
        let code = self.poll_xfer_completion(2_000_000)
            .ok_or(PCIeDeviceErr::InitFailure)?;
        if code != 1 && code != 13 {
            log::error!("xHCI: bulk IN failed (code={})", code);
            return Err(PCIeDeviceErr::InitFailure);
        }
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Phase 4c: MSC Bulk-Only Transport (BOT)
    // -------------------------------------------------------------------------

    /// Execute one BOT IN transaction: CBW → data IN → CSW.
    /// Returns CSW status byte (0 = pass).
    fn msc_bot_in(
        &mut self, slot: u8,
        cdb: &[u8; 16], cdb_len: u8,
        data_phys: u64, data_len: u32,
    ) -> Result<u8, PCIeDeviceErr> {
        let mut cbw_buf = DMAPool::<[u8; 64]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        let mut csw_buf = DMAPool::<[u8; 64]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        for b in cbw_buf.as_mut().iter_mut() { *b = 0; }
        for b in csw_buf.as_mut().iter_mut() { *b = 0; }

        self.msc_tag = self.msc_tag.wrapping_add(1);
        let tag = self.msc_tag;

        let cbw = msc::Cbw {
            signature: msc::CBW_SIGNATURE,
            tag,
            data_transfer_length: data_len,
            flags: msc::CBW_FLAGS_IN,
            lun: 0,
            cb_length: cdb_len,
            cb: *cdb,
        };
        msc::write_cbw(cbw_buf.as_mut(), &cbw);

        let cbw_phys = cbw_buf.get_phy_addr().as_usize() as u64;
        let csw_phys = csw_buf.get_phy_addr().as_usize() as u64;

        self.bulk_out_transfer(slot, cbw_phys, msc::CBW_WIRE_LEN as u32)?;
        if data_len > 0 {
            self.bulk_in_transfer(slot, data_phys, data_len)?;
        }
        self.bulk_in_transfer(slot, csw_phys, msc::CSW_WIRE_LEN as u32)?;

        let csw = msc::read_csw(csw_buf.as_mut());
        // Copy packed fields to locals before comparison to avoid misaligned-reference UB.
        let csw_sig = csw.signature;
        let csw_tag = csw.tag;
        let csw_status = csw.status;
        if csw_sig != msc::CSW_SIGNATURE {
            log::error!("xHCI: BOT: bad CSW signature {:#010x}", csw_sig);
            return Err(PCIeDeviceErr::InitFailure);
        }
        if csw_tag != tag {
            log::error!("xHCI: BOT: CSW tag mismatch ({} vs {})", csw_tag, tag);
            return Err(PCIeDeviceErr::InitFailure);
        }
        Ok(csw_status)
    }

    /// SCSI INQUIRY — confirm device type and log vendor/product strings.
    fn msc_inquiry(&mut self, slot: u8) -> Result<(), PCIeDeviceErr> {
        let mut buf = DMAPool::<[u8; 64]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        for b in buf.as_mut().iter_mut() { *b = 0; }
        let phys = buf.get_phy_addr().as_usize() as u64;

        let cdb = msc::scsi_inquiry_cdb();
        let st = self.msc_bot_in(slot, &cdb, 6, phys, 36)?;
        if st != msc::CSW_STATUS_PASS {
            log::error!("xHCI: INQUIRY failed (status={})", st);
            return Err(PCIeDeviceErr::InitFailure);
        }

        let d = buf.as_mut();
        let ptype = d[0] & 0x1f;
        // Trim trailing spaces from vendor (bytes 8-15) and product (bytes 16-31).
        let vendor = core::str::from_utf8(&d[8..16]).unwrap_or("?");
        let product = core::str::from_utf8(&d[16..32]).unwrap_or("?");
        log::info!(
            "xHCI: {}: slot {} INQUIRY type={} vendor='{}' product='{}'",
            self.name, slot, ptype,
            vendor.trim(), product.trim(),
        );
        Ok(())
    }

    /// SCSI READ CAPACITY(10) — returns (last_lba, block_len_bytes).
    fn msc_read_capacity(&mut self, slot: u8) -> Result<(u32, u32), PCIeDeviceErr> {
        let mut buf = DMAPool::<[u8; 64]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        for b in buf.as_mut().iter_mut() { *b = 0; }
        let phys = buf.get_phy_addr().as_usize() as u64;

        let cdb = msc::scsi_read_capacity_cdb();
        let st = self.msc_bot_in(slot, &cdb, 10, phys, 8)?;
        if st != msc::CSW_STATUS_PASS {
            log::error!("xHCI: READ CAPACITY failed (status={})", st);
            return Err(PCIeDeviceErr::InitFailure);
        }

        let d = buf.as_mut();
        let last_lba = u32::from_be_bytes([d[0], d[1], d[2], d[3]]);
        let block_len = u32::from_be_bytes([d[4], d[5], d[6], d[7]]);
        log::info!(
            "xHCI: {}: slot {} capacity: last_lba={} block={}B (~{}MiB)",
            self.name, slot, last_lba, block_len,
            (last_lba as u64 + 1) * block_len as u64 / (1024 * 1024),
        );
        Ok((last_lba, block_len))
    }

    /// SCSI READ(10) — read `count` 512-byte sectors from `lba` into `buf_phys`.
    pub fn msc_read10(
        &mut self, slot: u8, lba: u32, count: u16, buf_phys: u64,
    ) -> Result<(), PCIeDeviceErr> {
        let cdb = msc::scsi_read10_cdb(lba, count);
        let data_len = (count as u32) * 512;
        let st = self.msc_bot_in(slot, &cdb, 10, buf_phys, data_len)?;
        if st != msc::CSW_STATUS_PASS {
            log::error!("xHCI: READ(10) lba={} count={} failed (status={})", lba, count, st);
            return Err(PCIeDeviceErr::InitFailure);
        }
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Phase 4d: Top-level MSC setup orchestration
    // -------------------------------------------------------------------------

    fn try_setup_msc(&mut self, slot: u8) -> Result<(), PCIeDeviceErr> {
        let (cfg, cfg_len) = self.get_config_descriptor(slot)?;

        let info = match find_msc_bulk_endpoints(&cfg, cfg_len) {
            Some(i) => i,
            None => {
                log::info!(
                    "xHCI: {}: slot {} — no MSC bulk endpoints in config descriptor",
                    self.name, slot,
                );
                return Ok(());
            }
        };
        log::info!(
            "xHCI: {}: slot {} — MSC cfg={} IN={:#04x} OUT={:#04x} max_pkt={}",
            self.name, slot, info.config_val, info.in_addr, info.out_addr, info.max_pkt,
        );

        self.set_configuration(slot, info.config_val)?;
        self.configure_bulk_endpoints(slot, info.in_addr, info.out_addr, info.max_pkt)?;
        self.msc_inquiry(slot)?;

        let (last_lba, block_len) = self.msc_read_capacity(slot)?;
        if block_len != 512 {
            log::warn!(
                "xHCI: {}: slot {} — block size {} ≠ 512, skipping sector read",
                self.name, slot, block_len,
            );
            return Ok(());
        }

        // Read LBA 0 (MBR / protective GPT header).
        let mut sec = DMAPool::<[u8; 512]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        for b in sec.as_mut().iter_mut() { *b = 0; }
        let sec_phys = sec.get_phy_addr().as_usize() as u64;
        self.msc_read10(slot, 0, 1, sec_phys)?;

        // Extract partition table without keeping a long-lived borrow on sec.
        let boot_sig = {
            let s = sec.as_mut();
            u16::from_le_bytes([s[510], s[511]])
        };
        let mut fat32_part: Option<u32> = None;
        if boot_sig == 0xAA55 {
            log::info!("xHCI: {}: slot {} — valid MBR (0xAA55)", self.name, slot);
            for i in 0..4usize {
                let off = 446 + i * 16;
                let (ptype, status, lba_start, lba_size) = {
                    let s = sec.as_mut();
                    let pt = s[off + 4];
                    let st = s[off];
                    let ls = u32::from_le_bytes([s[off+8],  s[off+9],  s[off+10], s[off+11]]);
                    let lz = u32::from_le_bytes([s[off+12], s[off+13], s[off+14], s[off+15]]);
                    (pt, st, ls, lz)
                };
                if ptype == 0 { continue; }
                log::info!(
                    "  partition {}: type={:#04x} status={:#04x} lba_start={} lba_size={}",
                    i + 1, ptype, status, lba_start, lba_size,
                );
                if fat32_part.is_none() && (ptype == 0x0B || ptype == 0x0C) {
                    fat32_part = Some(lba_start);
                }
            }
        } else {
            log::warn!(
                "xHCI: {}: slot {} — no MBR signature ({:#06x}); total sectors: {}",
                self.name, slot, boot_sig, last_lba as u64 + 1,
            );
        }
        drop(sec);

        // Phase 5: mount FAT32 and locate kernel file.
        if let Some(plba) = fat32_part {
            self.try_mount_fat32(slot, plba);
        }
        Ok(())
    }
    // -------------------------------------------------------------------------
    // Phase 5: FAT32 filesystem layer
    // -------------------------------------------------------------------------

    /// Parse the BPB from `partition_lba` and store FAT32 volume metadata.
    fn fat32_mount(&mut self, slot: u8, partition_lba: u32) -> Result<(), PCIeDeviceErr> {
        let mut bpb = DMAPool::<[u8; 512]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        for b in bpb.as_mut().iter_mut() { *b = 0; }
        let phys = bpb.get_phy_addr().as_usize() as u64;
        self.msc_read10(slot, partition_lba, 1, phys)?;

        let fs = {
            let buf = bpb.as_mut();
            fat32::Fat32::from_bpb(buf, partition_lba).ok_or(PCIeDeviceErr::InitFailure)?
        };
        log::info!(
            "xHCI: {}: FAT32 bps={} spc={} fat_sz={} root_clus={} data_sec={}",
            self.name, fs.bytes_per_sec, fs.sec_per_clus,
            fs.fat_sz, fs.root_clus, fs.first_data_sec,
        );
        self.fat32 = Some(fs);
        Ok(())
    }

    /// Read the FAT32 cluster chain entry for `cluster`. Returns the next cluster
    /// number (≥ `fat32::EOC` means end-of-chain).
    fn fat32_next_cluster(&mut self, slot: u8, cluster: u32) -> Result<u32, PCIeDeviceErr> {
        let (fat_lba, byte_off) = {
            let fs = self.fat32.as_ref().ok_or(PCIeDeviceErr::InitFailure)?;
            fs.fat_entry_pos(cluster)
        };
        let mut sec = DMAPool::<[u8; 512]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        for b in sec.as_mut().iter_mut() { *b = 0; }
        let phys = sec.get_phy_addr().as_usize() as u64;
        self.msc_read10(slot, fat_lba, 1, phys)?;
        let raw = {
            let s = sec.as_mut();
            u32::from_le_bytes([s[byte_off], s[byte_off+1], s[byte_off+2], s[byte_off+3]])
        };
        Ok(raw & 0x0FFF_FFFF)
    }

    /// Scan the root directory cluster chain for a file named `filename`.
    /// Returns `Some((first_cluster, file_size))` on match, `None` if not found.
    fn fat32_find_root_file(
        &mut self, slot: u8, filename: &str,
    ) -> Result<Option<(u32, u32)>, PCIeDeviceErr> {
        let (mut cluster, sec_per_clus) = {
            let fs = self.fat32.as_ref().ok_or(PCIeDeviceErr::InitFailure)?;
            (fs.root_clus, fs.sec_per_clus)
        };
        let mut sec = DMAPool::<[u8; 512]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        // LFN accumulation buffer indexed by (seq-1)*13 + char_index.
        let mut lfn_buf = [0u16; 260];
        let mut lfn_valid = false;

        'chain: loop {
            let base_lba = {
                let fs = self.fat32.as_ref().ok_or(PCIeDeviceErr::InitFailure)?;
                fs.cluster_to_lba(cluster)
            };
            for s in 0..sec_per_clus as u32 {
                for b in sec.as_mut().iter_mut() { *b = 0; }
                let phys = sec.get_phy_addr().as_usize() as u64;
                self.msc_read10(slot, base_lba + s, 1, phys)?;

                for e in 0..16usize {
                    // Copy 32-byte entry to a local array to avoid borrow conflicts.
                    let entry: [u8; 32] = {
                        let d = sec.as_mut();
                        let off = e * 32;
                        let mut a = [0u8; 32];
                        a.copy_from_slice(&d[off..off + 32]);
                        a
                    };

                    if entry[0] == 0x00 { return Ok(None); } // end of directory
                    if entry[0] == 0xE5 { lfn_valid = false; continue; } // deleted

                    let attr = entry[11];
                    if attr == fat32::ATTR_LFN {
                        let order = entry[0];
                        if order & 0x40 != 0 {
                            // First-encountered LFN entry (highest seq, end of name).
                            for x in lfn_buf.iter_mut() { *x = 0; }
                            lfn_valid = true;
                        }
                        if lfn_valid {
                            let seq = (order & 0x1F) as usize;
                            if seq >= 1 && seq <= 20 {
                                let chars = fat32::lfn_chars(&entry);
                                let base = (seq - 1) * 13;
                                for (i, &c) in chars.iter().enumerate() {
                                    if base + i < 260 { lfn_buf[base + i] = c; }
                                }
                            }
                        }
                        continue;
                    }

                    // Skip volume labels and subdirectory entries.
                    if attr & (fat32::ATTR_VOLUME | fat32::ATTR_DIR) != 0 {
                        lfn_valid = false;
                        continue;
                    }

                    // Regular file entry: check LFN then 8.3 name.
                    let matched = (lfn_valid && fat32::lfn_matches(&lfn_buf, filename))
                        || fat32::match_83(&entry[..11], filename);
                    lfn_valid = false;

                    if matched {
                        let (fc, sz) = fat32::dir_entry_info(&entry);
                        return Ok(Some((fc, sz)));
                    }
                }
            }

            let next = self.fat32_next_cluster(slot, cluster)?;
            if next >= fat32::EOC { break 'chain; }
            cluster = next;
        }
        Ok(None)
    }

    /// Read `file_size` bytes of file data starting at `first_cluster` into
    /// the caller-provided DMA buffer at physical address `dest_phys`.
    pub fn fat32_read_file(
        &mut self, slot: u8, first_cluster: u32, file_size: u32, dest_phys: u64,
    ) -> Result<(), PCIeDeviceErr> {
        let sec_per_clus = {
            let fs = self.fat32.as_ref().ok_or(PCIeDeviceErr::InitFailure)?;
            fs.sec_per_clus
        };
        let clus_bytes = sec_per_clus as u32 * 512;
        let mut cluster = first_cluster;
        let mut remaining = file_size;
        let mut dest_off: u64 = 0;

        while remaining > 0 {
            let clus_lba = {
                let fs = self.fat32.as_ref().ok_or(PCIeDeviceErr::InitFailure)?;
                fs.cluster_to_lba(cluster)
            };
            let read_bytes = clus_bytes.min(remaining);
            let read_secs = ((read_bytes + 511) / 512) as u16;
            self.msc_read10(slot, clus_lba, read_secs, dest_phys + dest_off)?;

            remaining = remaining.saturating_sub(clus_bytes);
            dest_off += clus_bytes as u64;

            if remaining > 0 {
                let next = self.fat32_next_cluster(slot, cluster)?;
                if next >= fat32::EOC { break; }
                cluster = next;
            }
        }
        Ok(())
    }

    /// Mount the FAT32 partition at `partition_lba` and search the root directory
    /// for common kernel file names, logging what is found.
    fn try_mount_fat32(&mut self, slot: u8, partition_lba: u32) {
        if let Err(e) = self.fat32_mount(slot, partition_lba) {
            log::error!("xHCI: {}: FAT32 mount failed: {:?}", self.name, e);
            return;
        }
        let candidates = ["kernel.elf", "KERNEL.ELF", "vmlinux", "VMLINUX",
                          "boot.elf",   "BOOT.ELF"];
        for &name in &candidates {
            match self.fat32_find_root_file(slot, name) {
                Ok(Some((cluster, size))) => {
                    log::info!(
                        "xHCI: {}: '{}' found: first_cluster={} size={}B ({}KiB)",
                        self.name, name, cluster, size, size / 1024,
                    );
                }
                Ok(None) => {}
                Err(e) => {
                    log::warn!("xHCI: {}: scan '{}' error: {:?}", self.name, name, e);
                }
            }
        }
    }

    // -------------------------------------------------------------------------
    // Phase 6: CDC-ACM detection and setup orchestration
    // -------------------------------------------------------------------------

    /// Attempt to detect and configure a CDC-ACM USB serial adapter.
    /// Silently returns `Ok(())` when no CDC-ACM interface is present in the
    /// configuration descriptor.
    fn try_setup_cdcacm(&mut self, slot: u8) -> Result<(), PCIeDeviceErr> {
        let (cfg, cfg_len) = self.get_config_descriptor(slot)?;

        let info = match cdc_acm::find_cdcacm_endpoints(&cfg, cfg_len) {
            Some(i) => i,
            None => {
                log::info!(
                    "xHCI: {}: slot {} — no CDC-ACM endpoints in config descriptor",
                    self.name, slot,
                );
                return Ok(());
            }
        };

        log::info!(
            "xHCI: {}: slot {} — CDC-ACM cfg={} ctrl_if={} \
             IN={:#04x} OUT={:#04x} max_pkt={}",
            self.name, slot, info.config_val, info.ctrl_if_num,
            info.bulk_in_addr, info.bulk_out_addr, info.max_pkt,
        );

        self.set_configuration(slot, info.config_val)?;
        self.configure_bulk_endpoints(
            slot, info.bulk_in_addr, info.bulk_out_addr, info.max_pkt,
        )?;

        // Phase 7: line coding and control line state.
        self.cdcacm_set_line_coding(slot, info.ctrl_if_num, 115_200, 0, 0, 8)?;
        self.cdcacm_set_control_line_state(slot, info.ctrl_if_num, true, true)?;

        self.is_cdcacm    = true;
        self.cdcacm_ctrl_if = info.ctrl_if_num;
        self.cdcacm_max_pkt = info.max_pkt;

        // Phase 8: pre-allocate the DMA TX buffer used by cdcacm_write().
        let mut tx = DMAPool::<[u8; 512]>::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
        for b in tx.as_mut().iter_mut() { *b = 0; }
        self.cdcacm_tx_dma = Some(tx);

        log::info!(
            "xHCI: {}: slot {} — CDC-ACM ready (115200 8N1 DTR+RTS)",
            self.name, slot,
        );
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Context helper: write a little-endian u32 into a raw byte context page.
// ---------------------------------------------------------------------------

#[inline]
fn ctx_write32(ctx: &mut [u8], off: usize, val: u32) {
    ctx[off..off + 4].copy_from_slice(&val.to_le_bytes());
}

// ---------------------------------------------------------------------------
// MSC bulk endpoint discovery: walk config descriptor for class 0x08 + Bulk EPs.
// ---------------------------------------------------------------------------

struct BulkInfo {
    in_addr: u8,     // USB endpoint address (bit7=1)
    out_addr: u8,    // USB endpoint address (bit7=0)
    max_pkt: u16,
    config_val: u8,
}

fn find_msc_bulk_endpoints(desc: &[u8], len: usize) -> Option<BulkInfo> {
    let config_val = if len >= 6 { desc[5] } else { 1 };
    let mut i = 0;
    let mut in_msc = false;
    let mut in_ep: Option<u8> = None;
    let mut out_ep: Option<u8> = None;
    let mut max_pkt: u16 = 512;

    while i < len {
        let blen = desc[i] as usize;
        if blen < 2 || i + blen > len { break; }
        let btype = desc[i + 1];

        match btype {
            4 if blen >= 9 => {
                // Interface Descriptor: bInterfaceClass at [i+5].
                in_msc = desc[i + 5] == 0x08;
                if !in_msc {
                    in_ep = None;
                    out_ep = None;
                }
            }
            5 if blen >= 7 && in_msc => {
                // Endpoint Descriptor: only pick Bulk (bmAttributes bits[1:0] == 2).
                let addr = desc[i + 2];
                let attrs = desc[i + 3];
                let pkt = u16::from_le_bytes([desc[i + 4], desc[i + 5]]);
                if attrs & 0x3 == 2 {
                    max_pkt = pkt;
                    if addr & 0x80 != 0 { in_ep = Some(addr); }
                    else { out_ep = Some(addr); }
                }
            }
            _ => {}
        }
        i += blen;
    }

    match (in_ep, out_ep) {
        (Some(ia), Some(oa)) => Some(BulkInfo { in_addr: ia, out_addr: oa, max_pkt, config_val }),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Volatile MMIO helpers — keep BAR access explicit and never cached.
// ---------------------------------------------------------------------------

#[inline(always)]
unsafe fn rd8(base: VirtAddr, off: usize) -> u8 {
    core::ptr::read_volatile((base.as_usize() + off) as *const u8)
}

#[inline(always)]
unsafe fn rd16(base: VirtAddr, off: usize) -> u16 {
    core::ptr::read_volatile((base.as_usize() + off) as *const u16)
}

#[inline(always)]
unsafe fn rd32(base: VirtAddr, off: usize) -> u32 {
    core::ptr::read_volatile((base.as_usize() + off) as *const u32)
}

#[inline(always)]
unsafe fn wr32(base: VirtAddr, off: usize, val: u32) {
    core::ptr::write_volatile((base.as_usize() + off) as *mut u32, val)
}
