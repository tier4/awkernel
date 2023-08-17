use super::page_allocator::PageAllocator;
use x86_64::{
    structures::paging::{Mapper, OffsetPageTable, Page, PageTableFlags, PhysFrame, Size4KiB},
    PhysAddr, VirtAddr,
};

/// Map `phy_addr` to `virt_addr` with `flags`.
///
/// # Safety
///
/// `phy_addr` and `virt_addr` should not be used elsewhere.
/// You must know what you do by `map_to()` completely,
/// otherwise critical errors must be caused.
pub unsafe fn map_to<T>(
    phy_addr: usize,
    virt_addr: usize,
    flags: PageTableFlags,
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator<T>,
) -> bool
where
    T: Iterator<Item = PhysFrame> + Send,
{
    let frame = PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(phy_addr as u64));

    let page = Page::containing_address(VirtAddr::new(virt_addr as u64));

    unsafe {
        if let Ok(m) = page_table.map_to(page, frame, flags, page_allocator) {
            m.flush();
            true
        } else {
            false
        }
    }
}
