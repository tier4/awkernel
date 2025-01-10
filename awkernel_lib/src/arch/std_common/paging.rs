use crate::{
    addr::{phy_addr, virt_addr},
    paging::MapError,
};

impl crate::paging::Mapper for super::StdCommon {
    unsafe fn map(
        _vm_addr: virt_addr::VirtAddr,
        _phy_addr: phy_addr::PhyAddr,
        _flags: crate::paging::Flags,
    ) -> Result<(), MapError> {
        Err(MapError::InvalidPageTable)
    }

    unsafe fn unmap(_vm_addr: virt_addr::VirtAddr) {
        {}
    }

    fn vm_to_phy(_vm_addr: virt_addr::VirtAddr) -> Option<phy_addr::PhyAddr> {
        None
    }
}
