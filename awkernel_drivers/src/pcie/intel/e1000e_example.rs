//! This is a skelton of a PCIe device driver.

use alloc::{borrow::Cow, sync::Arc, vec::Vec};
use awkernel_lib::net::net_device::{self, NetDevice};

use crate::pcie::{pcie_id, PCIeDevice, PCIeDeviceErr, PCIeInfo};

const E1000_DEV_ID_82574L: u16 = 0x10D3;
const EECD: usize = 0x00010; // EEPROM Control Register

/// First, we need to check if the device is an Intel 82574L (e1000e).
/// This function is called by `crate::pcie::PCIeInfo::attach`
/// to check if the device is an Intel 82574L (e1000e).
pub fn match_device(vendor: u16, id: u16) -> bool {
    vendor == pcie_id::INTEL_VENDOR_ID && id == E1000_DEV_ID_82574L
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

    let e1000e = E1000eExample::new(info);
    let result = Arc::new(e1000e);

    // Add the network interface, if needed.
    awkernel_lib::net::add_interface(result.clone(), None);

    Ok(result)
}

pub struct E1000eExample {
    _info: PCIeInfo,
    // Add more fields if needed.
}

impl E1000eExample {
    fn new(info: PCIeInfo) -> Self {
        // Initialize the device.
        // For example, reset the device, initialize the registers, initialize interrupts, etc.

        if let Some(bar0) = info.get_bar(0) {
            if let Some(val) = bar0.read32(EECD) {
                log::info!("EECD = 0x{val:x}");
            }
        }

        Self { _info: info }
    }
}

impl PCIeDevice for E1000eExample {
    fn device_name(&self) -> Cow<'static, str> {
        "Intel 82574L (e1000e)".into()
    }
}

impl NetDevice for E1000eExample {
    fn add_multicast_addr(&self, _addr: &[u8; 6]) -> Result<(), net_device::NetDevError> {
        todo!("add_multicast_addr")
    }

    fn remove_multicast_addr(&self, _addr: &[u8; 6]) -> Result<(), net_device::NetDevError> {
        todo!("remove_multicast_addr");
    }

    fn can_send(&self) -> bool {
        todo!("can_send");
    }

    fn capabilities(&self) -> net_device::NetCapabilities {
        todo!("capabilities");
    }

    fn device_short_name(&self) -> Cow<'static, str> {
        "e1000e".into()
    }

    fn down(&self) -> Result<(), net_device::NetDevError> {
        todo!("down");
    }

    fn flags(&self) -> net_device::NetFlags {
        todo!("flags");
    }

    fn interrupt(&self, _irq: u16) -> Result<(), net_device::NetDevError> {
        todo!("interrupt");
    }

    fn irqs(&self) -> Vec<u16> {
        todo!("irqs");
    }

    fn link_speed(&self) -> u64 {
        todo!("link_speed");
    }

    fn link_status(&self) -> net_device::LinkStatus {
        todo!("link_status");
    }

    fn mac_address(&self) -> [u8; 6] {
        todo!("mac_address");
    }

    fn num_queues(&self) -> usize {
        todo!("num_queues");
    }

    fn recv(
        &self,
        _que_id: usize,
    ) -> Result<Option<net_device::EtherFrameBuf>, net_device::NetDevError> {
        todo!("recv");
    }

    fn send(
        &self,
        _data: net_device::EtherFrameRef,
        _que_id: usize,
    ) -> Result<(), net_device::NetDevError> {
        todo!("send");
    }

    fn up(&self) -> Result<(), net_device::NetDevError> {
        todo!("up");
    }

    fn rx_irq_to_que_id(&self, _irq: u16) -> Option<usize> {
        todo!("rx_irq_to_que_id");
    }
}
