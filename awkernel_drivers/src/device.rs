use awkernel_lib::paging::{Frame, FrameAllocator};

#[cfg(feature = "pcie")]
use crate::pcie::PCIeInfo;

#[derive(Debug)]
pub enum DeviceInfo {
    #[cfg(feature = "pcie")]
    PCIe(PCIeInfo),
    // USB,
}

pub trait Device<F, FA, E>
where
    F: Frame,
    FA: FrameAllocator<F, E>,
{
    fn match_device(info: &DeviceInfo) -> bool;
}
