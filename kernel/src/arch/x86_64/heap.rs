//! Allocate pages for heap memory.

use super::page_allocator::PageAllocator;
use crate::config::{HEAP_START, PAGE_SIZE};
use x86_64::{
    structures::paging::{FrameAllocator, Mapper, OffsetPageTable, Page, PageTableFlags},
    VirtAddr,
};

/// Map virtual memory of heap memory to physical memory.
/// Return the number of allocated pages from `HEAP_START`.
pub(super) fn map_heap(
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator,
    max_pages: usize,
) -> usize {
    let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;
    let mut num_pages = 0;

    for addr in (HEAP_START..).step_by(PAGE_SIZE as usize) {
        // Allocate a physical page.
        let Some(frame) = page_allocator.allocate_frame() else { return num_pages };

        // Map a virtual page to the physical memory.
        let page = Page::containing_address(VirtAddr::new(addr));
        unsafe {
            if let Ok(m) = page_table.map_to(page, frame, flags, page_allocator) {
                m.flush();
            } else {
                return num_pages;
            }
        };

        num_pages += 1;

        if num_pages >= max_pages {
            break;
        }
    }

    num_pages
}
