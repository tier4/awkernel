use crate::pcie::{pcie_id, PCIeDevice, PCIeDeviceErr, PCIeInfo};
use alloc::sync::Arc;

const VIRTIO_NET_ID: u16 = 0x1041;

pub fn match_device(vendor: u16, id: u16) -> bool {
    vendor == pcie_id::VIRTIO_VENDOR_ID && id == VIRTIO_NET_ID
}

pub fn attach(info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    // Non-transitional devices SHOULD have a PCI Revision ID of 1 or higher.
    if info.get_revision_id() == 0 {
        return Err(PCIeDeviceErr::RevisionIDMismatch);
    }

    // TODO: Implement
    log::info!("TODO: VirtIO-net attach() is to be implemented");
    Ok(info.unknown_device())
}
