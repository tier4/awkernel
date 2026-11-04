use super::{
    address::{PhysPageNum, VirtPageNum, PAGE_SIZE},
    page_table::{get_page_table, Flags},
    ArchImpl,
};
use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    paging::{MapError, Mapper},
};

impl Mapper for ArchImpl {
    unsafe fn map(
        vm_addr: VirtAddr,
        phy_addr: PhyAddr,
        flags: crate::paging::Flags,
    ) -> Result<(), MapError> {
        // Check if already mapped
        if Self::vm_to_phy(vm_addr).is_some() {
            return Err(MapError::AlreadyMapped);
        }

        let vm_addr_aligned = vm_addr.as_usize() & !(PAGE_SIZE - 1);
        let phy_addr_aligned = phy_addr.as_usize() & !(PAGE_SIZE - 1);

        // Get current page table
        if let Some(mut page_table) = get_page_table(VirtAddr::from_usize(vm_addr_aligned)) {
            let vpn = VirtPageNum::from(VirtAddr::from_usize(vm_addr_aligned));
            let ppn = PhysPageNum::from(PhyAddr::from_usize(phy_addr_aligned));

            let mut rv_flags = Flags::V | Flags::A;

            rv_flags |= Flags::R; // Always readable

            if flags.write {
                rv_flags |= Flags::W | Flags::D;
            }

            if flags.execute {
                rv_flags |= Flags::X;
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
        let vm_addr_aligned = VirtAddr::from_usize(vm_addr.as_usize() & !(PAGE_SIZE - 1));
        if let Some(mut page_table) = get_page_table(vm_addr_aligned) {
            let vpn = VirtPageNum::from(vm_addr_aligned);
            page_table.unmap(vpn);
        }
    }

    fn vm_to_phy(vm_addr: VirtAddr) -> Option<PhyAddr> {
        let higher = vm_addr.as_usize() & !(PAGE_SIZE - 1);
        let lower = vm_addr.as_usize() & (PAGE_SIZE - 1);

        if let Some(mut page_table) = get_page_table(VirtAddr::from_usize(higher)) {
            let vpn = VirtPageNum::from(VirtAddr::from_usize(higher));
            if let Some(pte) = page_table.translate(vpn) {
                if pte.is_valid() {
                    let ppn = pte.ppn();
                    let phy_addr = (ppn.0 << 12) | lower;
                    return Some(PhyAddr::from_usize(phy_addr));
                }
            }
        }
        None
    }
}
