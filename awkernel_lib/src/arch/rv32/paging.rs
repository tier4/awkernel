use crate::addr::{phy_addr::PhyAddr, virt_addr::VirtAddr};

impl crate::paging::Mapper for super::RV32 {
    unsafe fn map(_vm_addr: VirtAddr, _phy_addr: PhyAddr, _flags: crate::paging::Flags) -> bool {
        todo!()
    }

    unsafe fn unmap(_vm_addr: VirtAddr) {
        todo!()
    }

    fn vm_to_phy(_vm_addr: VirtAddr) -> Option<PhyAddr> {
        todo!()
    }
}
