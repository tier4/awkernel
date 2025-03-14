//! This is a skelton of a PCIe device driver.

use alloc::{borrow::Cow, sync::Arc, vec::Vec};
use awkernel_lib::net::net_device::{self, NetDevice};

use crate::pcie::{PCIeDevice, PCIeDeviceErr, PCIeInfo};

mod igc_hw;

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

    let igc = Igc::new(info);
    let result = Arc::new(igc);

    // Add the network interface, if needed.
    awkernel_lib::net::add_interface(result.clone(), None);

    Ok(result)
}

pub struct Igc {
    info: PCIeInfo,
    // Add more fields if needed.
}

impl Igc {
    fn new(info: PCIeInfo) -> Self {
        // TODO: Initialize the device.

        Self { info }
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
        // TODO
        [0; 6]
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
