use crate::pcie::{pcie_id, PCIeDevice, PCIeDeviceErr, PCIeInfo};
use alloc::sync::Arc;

const VIRTIO_NET_ID: u16 = 0x1000;

pub fn match_device(vendor: u16, id: u16) -> bool {
    vendor == pcie_id::VIRTIO_VENDOR_ID && id == VIRTIO_NET_ID
}

pub fn attach(info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    // TODO: Implement
    log::info!("TODO: VirtIO-net attach() is to be implemented");
    Ok(info.unknown_device())
}
