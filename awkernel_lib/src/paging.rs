use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr},
    memory::Flags,
};

pub trait Frame {
    fn start_address(&self) -> PhyAddr;
    fn set_address(&mut self, addr: PhyAddr);
    fn size(&self) -> usize;
}

/// Allocate a frame.
pub trait FrameAllocator<F, E>
where
    F: Frame,
{
    fn allocate_frame(&mut self) -> Result<F, E>;
}

pub trait PageTable<F, FA, E>
where
    F: Frame,
    FA: FrameAllocator<F, E>,
{
    unsafe fn map_to(
        &mut self,
        phy_addr: PhyAddr,
        virt_addr: VirtAddr,
        flags: Flags,
        page_allocator: &mut FA,
    ) -> Result<(), E>;
}
