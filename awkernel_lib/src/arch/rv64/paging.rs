use super::address::{PhysAddr as RVPhysAddr, PhysPageNum, VirtAddr as RVVirtAddr, VirtPageNum};
use super::page_table::get_page_table;
use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    paging::{MapError, PAGESIZE},
};

impl crate::paging::Mapper for super::RV64 {
    unsafe fn map(
        vm_addr: VirtAddr,
        phy_addr: PhyAddr,
        flags: crate::paging::Flags,
    ) -> Result<(), MapError> {
        // Check if already mapped
        if Self::vm_to_phy(vm_addr).is_some() {
            return Err(MapError::AlreadyMapped);
        }

        let vm_addr_aligned = vm_addr.as_usize() & !(PAGESIZE - 1);
        let phy_addr_aligned = phy_addr.as_usize() & !(PAGESIZE - 1);

        // Get current page table
        if let Some(mut page_table) = get_page_table(RVVirtAddr(vm_addr_aligned)) {
            let vpn = VirtPageNum::from(RVVirtAddr(vm_addr_aligned));
            let ppn = PhysPageNum::from(RVPhysAddr(phy_addr_aligned));

            let mut rv_flags = super::page_table::Flags::V | super::page_table::Flags::A;

            rv_flags |= super::page_table::Flags::R; // Always readable

            if flags.write {
                rv_flags |= super::page_table::Flags::W | super::page_table::Flags::D;
            }

            if flags.execute {
                rv_flags |= super::page_table::Flags::X;
            }

            if page_table.map(vpn, ppn, rv_flags) {
                Ok(())
            } else {
                Err(MapError::AlreadyMapped)
            }
        } else {
            Err(MapError::InvalidPageTable)
        }
    }

    unsafe fn unmap(vm_addr: VirtAddr) {
        let vm_addr_aligned = VirtAddr::new(vm_addr.as_usize() & !(PAGESIZE - 1));
        if let Some(mut page_table) = get_page_table(RVVirtAddr(vm_addr_aligned.as_usize())) {
            let vpn = VirtPageNum::from(RVVirtAddr(vm_addr_aligned.as_usize()));
            page_table.unmap(vpn);
        }
    }

    fn vm_to_phy(vm_addr: VirtAddr) -> Option<PhyAddr> {
        let higher = vm_addr.as_usize() & !(PAGESIZE - 1);
        let lower = vm_addr.as_usize() & (PAGESIZE - 1);

        if let Some(mut page_table) = get_page_table(RVVirtAddr(higher)) {
            let vpn = VirtPageNum::from(RVVirtAddr(higher));
            if let Some(pte) = page_table.translate(vpn) {
                if pte.is_valid() {
                    let ppn = pte.ppn();
                    let phy_addr = (ppn.0 << 12) | lower;
                    return Some(PhyAddr::new(phy_addr));
                }
            }
        }
        None
    }
}
