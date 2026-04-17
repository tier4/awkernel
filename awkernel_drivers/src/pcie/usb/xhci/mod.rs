use alloc::{borrow::Cow, boxed::Box, format, string::String, sync::Arc};
use awkernel_lib::{addr::{virt_addr::VirtAddr, Addr}, dma_pool::DMAPool};

// super       = crate::pcie::usb
// super::super = crate::pcie  (where PCIeDevice, PCIeDeviceErr, PCIeInfo, base_address live)
use super::super::{
    base_address::BaseAddress, PCIeDevice, PCIeDeviceErr, PCIeInfo,
};

mod regs;
mod ring;

use ring::{CommandRing, Dcbaa, EventRing, TransferRing, Trb};

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

    // Context size: 32 bytes (CSZ=0) or 64 bytes (CSZ=1). Decoded from HCCPARAMS1.
    ctx_size: usize,

    // Per-device state populated during enumeration (one device at a time for now).
    dev_slot: Option<u8>,
    ep0_ring: Option<TransferRing>,
    dev_ctx: Option<DMAPool<[u8; 4096]>>,
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

    // Map the MMIO region(s) declared in BARs and enable bus-master DMA.
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
    dev.program_rings();

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

    // Synchronous boot-time enumeration: find and address any device already connected.
    dev.boot_enumerate();

    Ok(Arc::new(dev))
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
            ctx_size,
            dev_slot: None,
            ep0_ring: None,
            dev_ctx: None,
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
        let id_vendor  = u16::from_le_bytes([d[8], d[9]]);
        let id_product = u16::from_le_bytes([d[10], d[11]]);
        let bcd_dev    = u16::from_le_bytes([d[12], d[13]]);

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

    /// Scan all ports for connected devices and enumerate the first one found.
    /// This is a blocking, synchronous scan intended for single-threaded boot code.
    pub fn boot_enumerate(&mut self) {
        // Give the controller time to power on ports and generate events (≤20ms USB2).
        for _ in 0..2_000_000u32 {
            core::hint::spin_loop();
        }
        self.drain_events();

        // Find the first port with a device connected.
        let mut found_port = None;
        for p in 1..=self.max_ports as usize {
            if self.read_portsc(p) & regs::port::CCS != 0 {
                found_port = Some(p);
                break;
            }
        }

        let port = match found_port {
            Some(p) => p,
            None => {
                log::info!("xHCI: {}: no device found at boot", self.name);
                return;
            }
        };

        log::info!("xHCI: {}: device detected on port {}", self.name, port);

        // Issue port reset and wait for PRC (Port Reset Change).
        let portsc = self.read_portsc(port);
        self.write_portsc(
            port,
            (portsc & !(regs::port::PED | regs::port::CHANGE_BITS)) | regs::port::PR,
        );
        if !self.poll_portsc(port, regs::port::PRC, regs::port::PRC, 2_000_000) {
            log::error!("xHCI: {}: port {} reset timeout", self.name, port);
            return;
        }
        // Clear change bits.
        let portsc = self.read_portsc(port);
        self.write_portsc(port, portsc & !(regs::port::PED | regs::port::CHANGE_BITS));
        self.drain_events();

        // Enable Slot.
        self.send_enable_slot();
        let (code, slot) = match self.poll_cmd_completion(2_000_000) {
            Some(r) => r,
            None => {
                log::error!("xHCI: {}: Enable Slot timeout", self.name);
                return;
            }
        };
        if code != 1 {
            log::error!("xHCI: {}: Enable Slot failed (code={})", self.name, code);
            return;
        }
        log::info!("xHCI: {}: slot {} assigned for port {}", self.name, slot, port);

        if let Err(e) = self.enumerate_port(port, slot) {
            log::error!("xHCI: {}: enumerate_port failed: {:?}", self.name, e);
        }
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
