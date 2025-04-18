use crate::pcie::PCIeDeviceErr;

pub mod virtio_common_config;
pub mod virtio_net_config;

#[derive(Debug)]
pub enum VirtioDriverErr {
    NoBar,
    ReadFailure,
}

impl From<VirtioDriverErr> for PCIeDeviceErr {
    fn from(value: VirtioDriverErr) -> Self {
        log::error!("virtio: {:?}", value);

        match value {
            VirtioDriverErr::ReadFailure => PCIeDeviceErr::ReadFailure,
            _ => PCIeDeviceErr::InitFailure,
        }
    }
}
