use alloc::sync::Arc;

use super::{PCIeDevice, PCIeDeviceErr, PCIeInfo};

#[cfg(feature = "virtio-net")]
pub mod virtio_net;

#[cfg(feature = "virtio-blk")]
pub mod virtio_blk;

pub(super) fn attach(info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    if virtio_net::match_device(info.vendor, info.id) {
        return virtio_net::attach(info);
    }

    if virtio_blk::match_device(info.vendor, info.id) {
        return virtio_blk::attach(info);
    }

    Ok(info.unknown_device())
}
