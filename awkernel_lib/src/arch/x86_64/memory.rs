use super::page_allocator::get_page_table;
use crate::{
    addr::{phy_addr, virt_addr, Addr},
    memory::PAGESIZE,
};
use x86_64::{
    structures::paging::{FrameAllocator, Mapper, Page, PageTableFlags, PhysFrame, Size4KiB},
    PhysAddr, VirtAddr,
};

impl crate::memory::Memory for super::X86 {
    unsafe fn map(
        vm_addr: virt_addr::VirtAddr,
        phy_addr: phy_addr::PhyAddr,
        flags: crate::memory::Flags,
    ) -> bool {
        let vm_addr = vm_addr.as_usize() & !(PAGESIZE - 1);
        let phy_addr = phy_addr.as_usize() & !(PAGESIZE - 1);

        let Some(mut page_table) = get_page_table() else {
            return false;
        };
        let Ok(page) = Page::<Size4KiB>::from_start_address(VirtAddr::new(vm_addr as u64)) else {
            return false;
        };
        let Ok(phy_frame) = PhysFrame::from_start_address(PhysAddr::new(phy_addr as u64)) else {
            return false;
        };

        let mut allocator = EmptyAllocator;

        let mut f = PageTableFlags::PRESENT;

        if !flags.execute {
            f |= PageTableFlags::NO_EXECUTE;
        }

        if flags.write {
            f |= PageTableFlags::WRITABLE;
        }

        let Ok(flusher) = page_table.map_to(page, phy_frame, f, &mut allocator) else {
            return false;
        };
        flusher.flush();

        true
    }

    unsafe fn unmap(vm_addr: virt_addr::VirtAddr) {
        let vm_addr = vm_addr.as_usize() & !(PAGESIZE - 1);

        let Some(mut page_table) = get_page_table() else {
            return;
        };
        let Ok(page) = Page::<Size4KiB>::from_start_address(VirtAddr::new(vm_addr as u64)) else {
            return;
        };

        let Ok((_, flusher)) = page_table.unmap(page) else {
            return;
        };
        flusher.flush();
    }

    fn vm_to_phy(vm_addr: virt_addr::VirtAddr) -> Option<phy_addr::PhyAddr> {
        let page_table = unsafe { get_page_table() }?;

        let higher = vm_addr.as_usize() & !(PAGESIZE - 1);

        let page = Page::<Size4KiB>::from_start_address(VirtAddr::new(higher as u64)).ok()?;
        let phy_frame = page_table.translate_page(page).ok()?;

        let lower = vm_addr.as_usize() & (PAGESIZE - 1);

        Some(phy_addr::PhyAddr::new(
            phy_frame.start_address().as_u64() as usize | lower,
        ))
    }
}

struct EmptyAllocator;

unsafe impl FrameAllocator<Size4KiB> for EmptyAllocator {
    fn allocate_frame(&mut self) -> Option<x86_64::structures::paging::PhysFrame<Size4KiB>> {
        None
    }
}
