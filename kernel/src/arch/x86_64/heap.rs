//! Allocate pages for heap memory.

use super::page_allocator::PageAllocator;
use crate::{
    config::{HEAP_SIZE, HEAP_START, PAGE_SIZE},
    heap::InitErr,
};
use x86_64::{
    structures::paging::{
        mapper::MapToError, FrameAllocator, Mapper, OffsetPageTable, Page, PageTableFlags, Size4KiB,
    },
    VirtAddr,
};

/// Map virtual memory of heap memory to physical memory.
pub(super) fn map_heap(
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
        // Allocate a page of physical memory.
        let frame = page_allocator
            .allocate_frame()
            .ok_or(InitErr::FailedToAllocateFrame)?;

        let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;

        // Map virtual memory to physical memory.
        unsafe {
            page_table
                .map_to(page, frame, flags, page_allocator)
                .or(Err(InitErr::FailedToMapPage))?
                .flush()
        };
    }

    Ok(())
}

/// Collect left heap memory
pub(super) unsafe fn collect_heap(
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator,
) -> Result<(), InitErr> {
    let start = VirtAddr::new(HEAP_START + HEAP_SIZE);
    let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;
    let mut addr = start;
    while let Some(frame) = page_allocator.allocate_frame() {
        let page: Page<Size4KiB> = Page::containing_address(addr);
        // Map virtual memory to physical memory.
        match page_table.map_to(page, frame, flags, page_allocator) {
            Ok(flush) => flush.flush(),
            Err(MapToError::FrameAllocationFailed) => break,
            Err(_) => return Err(InitErr::FailedToMapPage),
        }
        addr += PAGE_SIZE;
    }
    crate::heap::append(start.as_u64(), addr.as_u64());
    crate::config::ENLARGED_HEAP_SIZE = addr - start;
    Ok(())
}
