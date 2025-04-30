use crate::pcie::PCIeDeviceErr;
use core::fmt;

pub mod virtio_common_config;
pub mod virtio_net_config;

#[derive(Debug)]
pub enum VirtioDriverErr {
    NoBar,
    ReadFailure,
}

impl From<VirtioDriverErr> for PCIeDeviceErr {
    fn from(value: VirtioDriverErr) -> Self {
        log::error!("virtio: {value}");
        match value {
            VirtioDriverErr::ReadFailure => PCIeDeviceErr::ReadFailure,
            _ => PCIeDeviceErr::InitFailure,
        }
    }
}

impl fmt::Display for VirtioDriverErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReadFailure => write!(f, "Read failure."),
            Self::NoBar => write!(f, "No BAR."),
        }
    }
}
