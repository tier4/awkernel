use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr},
    paging::MapError,
};

impl crate::paging::Mapper for super::RV64 {
    unsafe fn map(
        _vm_addr: VirtAddr,
        _phy_addr: PhyAddr,
        _flags: crate::paging::Flags,
    ) -> Result<(), MapError> {
        todo!()
    }

    unsafe fn unmap(_vm_addr: VirtAddr) {
        todo!()
    }

    fn vm_to_phy(_vm_addr: VirtAddr) -> Option<PhyAddr> {
        todo!()
    }
}
