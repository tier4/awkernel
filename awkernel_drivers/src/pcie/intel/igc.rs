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
