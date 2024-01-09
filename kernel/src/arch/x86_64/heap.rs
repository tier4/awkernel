//! Allocate pages for heap memory.

use alloc::collections::BTreeMap;
use awkernel_lib::{
    arch::x86_64::page_allocator::{PageAllocator, VecPageAllocator},
    console::{unsafe_print_hex_u64, unsafe_puts},
    paging::PAGESIZE,
};
use x86_64::{
    structures::paging::{
        mapper::MapToError, FrameAllocator, Mapper, OffsetPageTable, Page, PageTableFlags,
        PhysFrame,
    },
    VirtAddr,
};

/// Map virtual memory of heap memory to physical memory.
/// Return the number of allocated pages from `HEAP_START`.
pub(super) fn map_backup_heap<T>(
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator<T>,
    start: usize,
    size: usize,
) -> usize
where
    T: Iterator<Item = PhysFrame> + Send,
{
    let flags = PageTableFlags::PRESENT
        | PageTableFlags::WRITABLE
        | PageTableFlags::NO_EXECUTE
        | PageTableFlags::GLOBAL;
    let mut num_pages = 0;

    for addr in (start..(start + size)).step_by(PAGESIZE) {
        // Allocate a physical page.
        let Some(frame) = page_allocator.allocate_frame() else {
            return num_pages;
        };

        // Map a virtual page to the physical memory.
        let page = Page::containing_address(VirtAddr::new(addr as u64));
        unsafe {
            match page_table.map_to(page, frame, flags, page_allocator) {
                Ok(m) => {
                    m.flush();
                }
                Err(MapToError::PageAlreadyMapped(f)) => {
                    unsafe_puts("error: MapToError::PageAlreadyMapped(0x");
                    unsafe_print_hex_u64(f.start_address().as_u64());
                    unsafe_puts(")\r\n");
                    return num_pages;
                }
                _ => {
                    return num_pages;
                }
            }
        };

        num_pages += 1;
    }

    num_pages
}

pub(super) fn map_primary_heap(
    page_table: &mut OffsetPageTable<'static>,
    page_allocators: &mut BTreeMap<u32, VecPageAllocator>,
    start: usize,
) -> usize {
    let flags = PageTableFlags::PRESENT
        | PageTableFlags::WRITABLE
        | PageTableFlags::NO_EXECUTE
        | PageTableFlags::GLOBAL;
    let mut num_pages = 0;
    let mut addr = start;

    for (_, page_allocator) in page_allocators.iter_mut() {
        while let Some(frame) = page_allocator.allocate_frame() {
            // Map a virtual page to the physical memory.
            let page = Page::containing_address(VirtAddr::new(addr as u64));
            unsafe {
                match page_table.map_to(page, frame, flags, page_allocator) {
                    Ok(m) => {
                        m.flush();
                        addr += PAGESIZE;
                        num_pages += 1;
                    }
                    Err(MapToError::PageAlreadyMapped(f)) => {
                        unsafe_puts("error: MapToError::PageAlreadyMapped(0x");
                        unsafe_print_hex_u64(f.start_address().as_u64());
                        unsafe_puts(")\r\n");
                        return num_pages;
                    }
                    Err(_) => {
                        break;
                    }
                }
            };
        }
    }

    num_pages
}
