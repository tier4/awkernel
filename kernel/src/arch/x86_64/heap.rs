use crate::{
    config::{HEAP_SIZE, HEAP_START},
    heap::InitErr,
};
use bootloader_api::{info::MemoryRegionKind, BootInfo};
use x86_64::{
    structures::paging::{
        FrameAllocator, Mapper, OffsetPageTable, Page, PageTableFlags, PhysFrame, Size4KiB,
    },
    PhysAddr, VirtAddr,
};

pub struct HeapMapper;

impl HeapMapper {
    pub(super) fn init(
        boot_info: &BootInfo,
        page_table: &mut OffsetPageTable<'static>,
    ) -> Result<(), InitErr> {
        let page_range = {
            let heap_start = VirtAddr::new(HEAP_START);
            let heap_end = heap_start + HEAP_SIZE - 1u64;
            let heap_start_page: Page<Size4KiB> = Page::containing_address(heap_start);
            let heap_end_page: Page<_> = Page::containing_address(heap_end);
            Page::range_inclusive(heap_start_page, heap_end_page)
        };

        let mut frames = boot_info
            .memory_regions
            .iter()
            .filter(|m| m.kind == MemoryRegionKind::Usable)
            .flat_map(|m| (m.start..m.end).step_by(4096))
            .map(|addr| PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(addr)));
        let mut frame_allocator = PageAllocator::new(&mut frames);

        for page in page_range {
            let frame = frame_allocator
                .allocate_frame()
                .ok_or(InitErr::FailedToAllocateFrame)?;

            let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE;

            unsafe {
                page_table
                    .map_to(page, frame, flags, &mut frame_allocator)
                    .or(Err(InitErr::FailedToMapPage))?
                    .flush()
            };
        }

        Ok(())
    }
}

struct PageAllocator<'a> {
    frames: &'a mut dyn Iterator<Item = PhysFrame>,
}

impl<'a> PageAllocator<'a> {
    fn new(frames: &'a mut dyn Iterator<Item = PhysFrame>) -> Self {
        PageAllocator { frames }
    }
}

unsafe impl<'a> FrameAllocator<Size4KiB> for PageAllocator<'a> {
    fn allocate_frame(&mut self) -> Option<PhysFrame<Size4KiB>> {
        self.frames.next()
    }
}
