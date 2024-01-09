use awkernel_lib::paging::{Frame, FrameAllocator};

use crate::pcie::PCIeInfo;

#[derive(Debug)]
pub enum DeviceInfo {
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
