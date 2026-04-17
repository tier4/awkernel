use alloc::{borrow::Cow, boxed::Box, format, string::String, sync::Arc};
use awkernel_lib::addr::{virt_addr::VirtAddr, Addr};

// super       = crate::pcie::usb
// super::super = crate::pcie  (where PCIeDevice, PCIeDeviceErr, PCIeInfo, base_address live)
use super::super::{
    base_address::BaseAddress, PCIeDevice, PCIeDeviceErr, PCIeInfo,
};

mod regs;
mod ring;

use ring::{CommandRing, Dcbaa, EventRing};

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
