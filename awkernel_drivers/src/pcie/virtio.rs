use alloc::sync::Arc;

use super::{PCIeDevice, PCIeDeviceErr, PCIeInfo};

pub mod config;

#[cfg(feature = "virtio-net")]
pub mod virtio_net;

#[cfg(feature = "virtio-blk")]
pub mod virtio_blk;

pub(super) fn attach(info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    #[cfg(feature = "virtio-net")]
    if virtio_net::match_device(info.vendor, info.id) {
        return virtio_net::attach(info);
    }

    #[cfg(feature = "virtio-blk")]
    if virtio_blk::match_device(info.vendor, info.id) {
        return virtio_blk::attach(info);
    }

    Ok(info.unknown_device())
}
