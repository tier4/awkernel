//! This is a skelton of a PCIe device driver.

use alloc::{borrow::Cow, boxed::Box, sync::Arc, vec::Vec};
use awkernel_lib::net::net_device::{self, NetDevice};
use i225::{igc_get_flash_presence_i225, I225Flash, I225NoFlash};
use igc_api::{igc_set_mac_type, igc_setup_init_funcs};
use igc_defines::*;
use igc_hw::{IgcHw, IgcMacType, IgcMediaType, IgcOperations};

use crate::pcie::{PCIeDevice, PCIeDeviceErr, PCIeInfo};

mod i225;
mod igc_api;
mod igc_base;
mod igc_defines;
mod igc_hw;
mod igc_mac;
mod igc_nvm;
mod igc_phy;
mod igc_regs;

const AUTONEG_ADV_DEFAULT: u16 = ADVERTISE_10_HALF
    | ADVERTISE_10_FULL
    | ADVERTISE_100_HALF
    | ADVERTISE_100_FULL
    | ADVERTISE_1000_FULL
    | ADVERTISE_2500_FULL;

const AUTO_ALL_MODES: u8 = 0;

const IGC_TXPBSIZE: u32 = 20408;
const IGC_DMCTLX_DCFLUSH_DIS: u32 = 0x80000000; // Disable DMA Coalesce Flush

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IgcDriverErr {
    NoBar0,
    ReadFailure,
    MacInit,
    MasterRequestsPending,
    Reset,
    NVM,
    SwfwSync,
    BlkPhyReset,
    Param,
    Phy,
    Config,
}

/// Check if the device is an Intel I225/I226.
pub fn match_device(vendor: u16, id: u16) -> bool {
    igc_hw::IGC_DEVICES.contains(&(vendor, id))
}

/// Attach the device to the system.
/// This function is also called by `crate::pcie::PCIeInfo::attach`
/// to attach the device to the system.
pub fn attach(mut info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    // Initialize PCIeInfo

    // Map the memory regions of MMIO.
    if let Err(e) = info.map_bar() {
        log::warn!("Failed to map the memory regions of MMIO: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }

    // Read capabilities of PCIe.
    info.read_capability();

    let igc = Igc::new(info)?;

    let result = Arc::new(igc);

    // Add the network interface, if needed.
    awkernel_lib::net::add_interface(result.clone(), None);

    Ok(result)
}

pub struct Igc {
    info: PCIeInfo,
    hw: IgcHw,
    ops: Box<dyn IgcOperations + Sync + Send>, // Add more fields if needed.
}

impl Igc {
    fn new(mut info: PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        use PCIeDeviceErr::InitFailure;

        let mut hw = IgcHw::default();
        hw.device_id = info.id;

        igc_set_mac_type(&mut hw).or(Err(InitFailure))?;

        // TODO:
        // - allocate PCIe resources.
        // - allocate tx/rx queues.

        let ops = igc_setup_init_funcs(&mut info, &mut hw).or(Err(InitFailure))?;

        hw.mac.autoneg = true;
        hw.phy.autoneg_wait_to_complete = false;
        hw.phy.autoneg_advertised = AUTONEG_ADV_DEFAULT;

        // Copper options.
        if hw.phy.media_type == IgcMediaType::Copper {
            hw.phy.mdix = AUTO_ALL_MODES;
        }

        // Set the max frame size.
        hw.mac.max_frame_size = 9234;

        // TODO: Allocate multicast array memory.

        if ops.check_reset_block(&mut info).is_err() {
            log::info!("PHY reset is blocked due to SOL/IDER session");
        }

        // Disable Energy Efficient Ethernet (EEE).
        hw.dev_spec.eee_disable = true;

        ops.reset_hw(&mut info, &mut hw).or(Err(InitFailure))?;

        // Make sure we have a good EEPROM before we read from it.
        if ops.validate(&mut info, &mut hw).is_err() {
            // Some PCI-E parts fail the first check due to
            // the link being in sleep state, call it again,
            // if it fails a second time its a real issue.
            ops.validate(&mut info, &mut hw).or(Err(InitFailure))?;
        }

        ops.read_mac_addr(&mut info, &mut hw).or(Err(InitFailure))?;

        // TODO: continue initialization

        Ok(Igc { info, hw, ops })
    }
}

impl PCIeDevice for Igc {
    fn device_name(&self) -> Cow<'static, str> {
        "Intel I225/I226 2.5 GbE".into()
    }
}

impl NetDevice for Igc {
    fn add_multicast_addr(&self, _addr: &[u8; 6]) -> Result<(), net_device::NetDevError> {
        todo!("add_multicast_addr")
    }

    fn remove_multicast_addr(&self, _addr: &[u8; 6]) -> Result<(), net_device::NetDevError> {
        todo!("remove_multicast_addr");
    }

    fn can_send(&self) -> bool {
        // TODO
        false
    }

    fn capabilities(&self) -> net_device::NetCapabilities {
        // TODO
        net_device::NetCapabilities::empty()
    }

    fn device_short_name(&self) -> Cow<'static, str> {
        "igc".into()
    }

    fn down(&self) -> Result<(), net_device::NetDevError> {
        // TODO
        Ok(())
    }

    fn flags(&self) -> net_device::NetFlags {
        // TODO
        net_device::NetFlags::empty()
    }

    fn interrupt(&self, _irq: u16) -> Result<(), net_device::NetDevError> {
        todo!("interrupt");
    }

    fn irqs(&self) -> Vec<u16> {
        // TODO
        Vec::new()
    }

    fn link_speed(&self) -> u64 {
        // TODO
        0
    }

    fn link_status(&self) -> net_device::LinkStatus {
        // TODO
        net_device::LinkStatus::Down
    }

    fn mac_address(&self) -> [u8; 6] {
        self.hw.mac.addr
    }

    fn num_queues(&self) -> usize {
        // TODO
        1
    }

    fn recv(
        &self,
        _que_id: usize,
    ) -> Result<Option<net_device::EtherFrameBuf>, net_device::NetDevError> {
        // TODO
        Ok(None)
    }

    fn send(
        &self,
        _data: net_device::EtherFrameRef,
        _que_id: usize,
    ) -> Result<(), net_device::NetDevError> {
        // TODO
        Ok(())
    }

    fn up(&self) -> Result<(), net_device::NetDevError> {
        // TODO
        Ok(())
    }

    fn rx_irq_to_que_id(&self, _irq: u16) -> Option<usize> {
        // TODO
        None
    }
}

#[inline(always)]
fn write_flush(info: &PCIeInfo) -> Result<(), IgcDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.read32(igc_regs::IGC_STATUS)
        .ok_or(IgcDriverErr::ReadFailure)?;
    Ok(())
}

#[inline(always)]
fn read_reg(info: &PCIeInfo, offset: usize) -> Result<u32, IgcDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.read32(offset).ok_or(IgcDriverErr::ReadFailure)
}

#[inline(always)]
fn write_reg(info: &PCIeInfo, offset: usize, value: u32) -> Result<(), IgcDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.write32(offset, value);
    Ok(())
}

#[inline(always)]
fn read_reg_array(info: &PCIeInfo, offset: usize, index: usize) -> Result<u32, IgcDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.read32(offset + (index << 2))
        .ok_or(IgcDriverErr::ReadFailure)
}

#[inline(always)]
fn write_reg_array(
    info: &PCIeInfo,
    offset: usize,
    index: usize,
    value: u32,
) -> Result<(), IgcDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.write32(offset + (index << 2), value);
    Ok(())
}

/// Initialize the DMA Coalescing feature
fn igc_init_dmac(
    info: &mut PCIeInfo,
    hw: &IgcHw,
    pba: u32,
    sc_dmac: u32,
) -> Result<(), IgcDriverErr> {
    use igc_regs::*;

    let reg = !IGC_DMACR_DMAC_EN;

    let max_frame_size = hw.mac.max_frame_size;

    if sc_dmac == 0 {
        // Disabling it
        write_reg(info, IGC_DMACR, reg)?;
        return Ok(());
    } else {
        log::info!("igc: DMA Coalescing enabled");
    }

    // Set starting threshold
    write_reg(info, IGC_DMCTXTH, 0)?;

    let hwm = 64 * pba - max_frame_size / 16;
    let hwm = if hwm < 64 * (pba - 6) {
        64 * (pba - 6)
    } else {
        hwm
    };

    let mut reg = read_reg(info, IGC_FCRTC)?;
    reg &= !IGC_FCRTC_RTH_COAL_MASK;
    reg |= (hwm << IGC_FCRTC_RTH_COAL_SHIFT) & IGC_FCRTC_RTH_COAL_MASK;
    write_reg(info, IGC_FCRTC, reg)?;

    let dmac = pba - max_frame_size / 512;
    let dmac = if dmac < pba - 10 { pba - 10 } else { dmac };
    let mut reg = read_reg(info, IGC_DMACR)?;
    reg &= !IGC_DMACR_DMACTHR_MASK;
    reg |= (dmac << IGC_DMACR_DMACTHR_SHIFT) & IGC_DMACR_DMACTHR_MASK;

    // transition to L0x or L1 if available
    reg |= IGC_DMACR_DMAC_EN | IGC_DMACR_DMAC_LX_MASK;

    // Check if status is 2.5Gb backplane connection
    // before configuration of watchdog timer, which is
    // in msec values in 12.8usec intervals
    // watchdog timer= msec values in 32usec intervals
    // for non 2.5Gb connection
    let status = read_reg(info, IGC_STATUS)?;
    if status & IGC_STATUS_2P5_SKU != 0 && status & IGC_STATUS_2P5_SKU_OVER != 0 {
        reg |= (sc_dmac * 5) >> 6;
    } else {
        reg |= sc_dmac >> 5;
    }

    write_reg(info, IGC_DMACR, reg)?;

    write_reg(info, IGC_DMCRTRH, 0)?;

    // Set the interval before transition
    let mut reg = read_reg(info, IGC_DMCTLX)?;
    reg |= IGC_DMCTLX_DCFLUSH_DIS;

    // in 2.5Gb connection, TTLX unit is 0.4 usec
    // which is 0x4*2 = 0xA. But delay is still 4 usec
    let status = read_reg(info, IGC_STATUS)?;
    if status & IGC_STATUS_2P5_SKU != 0 && status & IGC_STATUS_2P5_SKU_OVER != 0 {
        reg |= 0xA;
    } else {
        reg |= 0x4;
    }

    write_reg(info, IGC_DMCTLX, reg)?;

    // free space in tx packet buffer to wake from DMA coal
    write_reg(
        info,
        IGC_DMCTXTH,
        (IGC_TXPBSIZE - (2 * max_frame_size)) >> 6,
    )?;

    // make low power state decision controlled by DMA coal
    let mut reg = read_reg(info, IGC_PCIEMISC)?;
    reg &= !IGC_PCIEMISC_LX_DECISION;
    write_reg(info, IGC_PCIEMISC, reg)?;

    Ok(())
}
