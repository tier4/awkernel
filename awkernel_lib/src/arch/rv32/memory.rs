use super::page_table::{Flags, PageTable, get_page_table};
use alloc::vec::Vec;
use super::address::{VirtAddr, VirtPageNum, PhysPageNum, PhysAddr};

/// We should set memory end based on specific device
pub const MEMORY_END: u64 = 0x88000000;

pub struct Memory;

impl crate::memory::Memory for Memory {
    unsafe fn map(vm_addr: usize, phy_addr: usize, flags: crate::memory::Flags) -> bool {
        let va: VirtAddr = vm_addr.into();
        let vpn: VirtPageNum = va.into();
        let Some(mut page_table) = get_page_table(va) else { return false };
        let pa: PhysAddr = phy_addr.into();
        let ppn: PhysPageNum = pa.into();
        page_table.map(vpn, ppn, flags)
    }

    unsafe fn unmap(vm_addr: usize) {
        let va: VirtAddr = vm_addr.into();
        let vpn: VirtPageNum = va.into();
        let Some(mut page_table) = get_page_table(va) else { return };
        page_table.unmap(vpn);
    }

    fn vm_to_phy(vm_addr: usize) -> Option<usize> {
        todo!()
    }
}
