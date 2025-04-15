use crate::pcie::{pcie_id, PCIeDevice, PCIeDeviceErr, PCIeInfo};
use alloc::sync::Arc;

const VIRTIO_NET_ID: u16 = 0x1000;

pub fn match_device(vendor: u16, id: u16) -> bool {
    vendor == pcie_id::VIRTIO_VENDOR_ID && id == VIRTIO_NET_ID
}

pub fn attach(mut info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    // Initialize PCIeInfo

    // Map the memory regions of MMIO.
    if let Err(e) = info.map_bar() {
        log::warn!("Failed to map the memory regions of MMIO: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }

    // Read capabilities of PCIe.
    info.read_capability();

    // TODO: Implement
    log::info!("TODO: VirtIO-net attach() is to be implemented");
    Ok(info.unknown_device())
}
