use bootloader_api::BootInfo;
use x86_64::{
    registers::control::Cr3,
    structures::paging::{FrameAllocator, OffsetPageTable, PageTable, PhysFrame, Size4KiB},
    VirtAddr,
};
use synctools::mcs::{MCSLock, MCSNode};

pub struct PageAllocator<'a> {
    frames: MCSLock<&'a mut dyn Iterator<Item = PhysFrame>>,
}

impl<'a> PageAllocator<'a> {
    pub fn new(frames: &'a mut dyn Iterator<Item = PhysFrame>) -> Self {
        PageAllocator { frames : MCSLock::new(frames) }
    }
}

unsafe impl<'a> FrameAllocator<Size4KiB> for PageAllocator<'a> {
    fn allocate_frame(&mut self) -> Option<PhysFrame<Size4KiB>> {
        let mut node = MCSNode::new();
        let mut guard = self.frames.lock(&mut node);
        guard.next()
    }
}

pub unsafe fn get_page_table(boot_info: &BootInfo) -> Option<OffsetPageTable<'static>> {
    let physical_memory_offset = VirtAddr::new(*boot_info.physical_memory_offset.as_ref()?);

    let level_4_table = active_level_4_table(physical_memory_offset);
    Some(OffsetPageTable::new(level_4_table, physical_memory_offset))
}

unsafe fn active_level_4_table(physical_memory_offset: VirtAddr) -> &'static mut PageTable {
    let (level_4_table_frame, _) = Cr3::read();

    let phys = level_4_table_frame.start_address();
    let virt = physical_memory_offset + phys.as_u64();
    let ptr = virt.as_mut_ptr() as *mut PageTable;

    &mut *ptr
}
