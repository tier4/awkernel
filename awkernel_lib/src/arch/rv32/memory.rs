use super::page_table::{Flags, PageTable};
use alloc::vec::Vec;
use super::address::{VirtAddr, VirtPageNum, PhysPageNum, PhysAddr};

/// We should set memory end based on specific device
pub const MEMORY_END: u64 = 0x88000000;

pub struct Memory {
    page_table: PageTable,
}

impl crate::memory::Memory for Memory {
    unsafe fn map(vm_addr: usize, phy_addr: usize, flags: crate::memory::Flags) -> bool {
        let va: VirtAddr = vm_addr.into();
        let vpn: VirtPageNum = va.into();
    }

    unsafe fn unmap(vm_addr: usize) {
        todo!()
    }

    fn vm_to_phy(vm_addr: usize) -> Option<usize> {
        todo!()
    }
}
