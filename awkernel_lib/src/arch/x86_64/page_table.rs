use super::PageAllocator;
use crate::addr::Addr;
use x86_64::{
    structures::paging::{Mapper, OffsetPageTable, Page, PageTableFlags, PhysFrame, Size4KiB},
    PhysAddr, VirtAddr,
};

pub struct PageTable<'a> {
    offset_page_table: &'a mut OffsetPageTable<'static>,
}

impl<'a> PageTable<'a> {
    pub fn new(offset_page_table: &'a mut OffsetPageTable<'static>) -> Self {
        Self { offset_page_table }
    }
}

impl<'a, 'b, T: Iterator<Item = PhysFrame> + Send>
    crate::paging::PageTable<super::page_allocator::Frame, PageAllocator<'a, T>, ()>
    for PageTable<'b>
{
    unsafe fn map_to(
        &mut self,
        phy_addr: crate::addr::phy_addr::PhyAddr,
        virt_addr: crate::addr::virt_addr::VirtAddr,
        flags: crate::paging::Flags,
        page_allocator: &mut super::page_allocator::PageAllocator<'a, T>,
    ) -> Result<(), ()> {
        let flags = flags_to_x86_flags(flags);

        let page = Page::containing_address(VirtAddr::new(virt_addr.as_usize() as u64));
        let frame =
            PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(phy_addr.as_usize() as u64));

        if let Ok(_) = self
            .offset_page_table
            .map_to(page, frame, flags, page_allocator)
        {
            Ok(())
        } else {
            Err(())
        }
    }
}

fn flags_to_x86_flags(flags: crate::paging::Flags) -> PageTableFlags {
    let mut x86_flags = PageTableFlags::PRESENT;

    if flags.write {
        x86_flags |= PageTableFlags::WRITABLE;
    }

    if !flags.execute {
        x86_flags |= PageTableFlags::NO_EXECUTE;
    }

    if !flags.cache {
        x86_flags |= PageTableFlags::NO_CACHE;
    }

    if flags.write_through {
        x86_flags |= PageTableFlags::WRITE_THROUGH;
    }

    x86_flags
}
