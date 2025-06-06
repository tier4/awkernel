use super::address::VirtPageNum;
use super::page_table::{get_page_table, Flags};
use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    paging::MapError,
};

impl crate::paging::Mapper for super::RV32 {
    unsafe fn map(
        vm_addr: VirtAddr,
        phy_addr: PhyAddr,
        flags: crate::paging::Flags,
    ) -> Result<(), MapError> {
        // Check address alignment
        if !vm_addr.aligned() || !phy_addr.aligned() {
            return Err(MapError::AddressNotAligned);
        }

        // Get current page table
        if let Some(mut page_table) = get_page_table(vm_addr) {
            let vpn = VirtPageNum::from(vm_addr);
            let ppn = phy_addr.floor();

            // Convert common flags to RV32 flags
            let mut rv_flags = Flags::V | Flags::A; // Always valid and accessed

            if flags.write {
                rv_flags |= Flags::W | Flags::D; // Writable and dirty
            }

            rv_flags |= Flags::R; // Always readable

            if flags.execute {
                rv_flags |= Flags::X;
            }

            // Try to map the page
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
        if let Some(mut page_table) = get_page_table(vm_addr) {
            let vpn = VirtPageNum::from(vm_addr);
            page_table.unmap(vpn);
        }
    }

    fn vm_to_phy(vm_addr: VirtAddr) -> Option<PhyAddr> {
        if let Some(mut page_table) = get_page_table(vm_addr) {
            let vpn = VirtPageNum::from(vm_addr);
            if let Some(pte) = page_table.translate(vpn) {
                if pte.is_valid() {
                    let ppn = pte.ppn();
                    let phy_page_addr: PhyAddr = ppn.into();
                    let offset = vm_addr.page_offset();
                    return Some(PhyAddr::new(phy_page_addr.as_usize() + offset));
                }
            }
        }
        None
    }
}
