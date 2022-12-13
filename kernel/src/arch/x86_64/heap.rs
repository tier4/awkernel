use super::page_allocator::PageAllocator;
use crate::{
    config::{HEAP_SIZE, HEAP_START},
    heap::InitErr,
};
use bootloader_api::BootInfo;
use x86_64::{
    structures::paging::{FrameAllocator, Mapper, OffsetPageTable, Page, PageTableFlags, Size4KiB},
    VirtAddr,
};

pub struct HeapMapper;

impl HeapMapper {
    pub(super) fn init(
        boot_info: &BootInfo,
        page_table: &mut OffsetPageTable<'static>,
        page_allocator: &mut PageAllocator,
    ) -> Result<(), InitErr> {
        let page_range = {
            let heap_start = VirtAddr::new(HEAP_START);
            let heap_end = heap_start + HEAP_SIZE - 1u64;
            let heap_start_page: Page<Size4KiB> = Page::containing_address(heap_start);
            let heap_end_page: Page<_> = Page::containing_address(heap_end);
            Page::range_inclusive(heap_start_page, heap_end_page)
        };

        for page in page_range {
            let frame = page_allocator
                .allocate_frame()
                .ok_or(InitErr::FailedToAllocateFrame)?;

            let flags =
                PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;

            unsafe {
                page_table
                    .map_to(page, frame, flags, page_allocator)
                    .or(Err(InitErr::FailedToMapPage))?
                    .flush()
            };
        }

        Ok(())
    }
}
