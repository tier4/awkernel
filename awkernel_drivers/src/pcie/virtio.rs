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

#[derive(Debug)]
pub enum VirtioDriverErr {
    NoBar,
    ReadFailure,
    NoCap,
    InitFailure,
    NoVirtqueue,
    InvalidQueueSize,
    DMAPool,
    NoSlot,
    NeedReset,
}

impl From<VirtioDriverErr> for PCIeDeviceErr {
    fn from(value: VirtioDriverErr) -> Self {
        log::error!("virtio: {value:?}");
        match value {
            VirtioDriverErr::NoBar => PCIeDeviceErr::InitFailure,
            VirtioDriverErr::NoCap => PCIeDeviceErr::InitFailure,
            VirtioDriverErr::ReadFailure => PCIeDeviceErr::ReadFailure,
            VirtioDriverErr::InitFailure => PCIeDeviceErr::InitFailure,
            VirtioDriverErr::NoVirtqueue => PCIeDeviceErr::InitFailure,
            VirtioDriverErr::InvalidQueueSize => PCIeDeviceErr::InitFailure,
            VirtioDriverErr::DMAPool => PCIeDeviceErr::InitFailure,
            VirtioDriverErr::NoSlot => PCIeDeviceErr::InitFailure,
            VirtioDriverErr::NeedReset => PCIeDeviceErr::InitFailure,
        }
    }
}
