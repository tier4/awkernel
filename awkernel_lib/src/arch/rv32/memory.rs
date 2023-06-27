use crate::{
    page_table::Flags,
};

pub struct Memory;

impl crate::memory::Memory for Memory {
    unsafe fn map(vm_addr: usize, phy_addr: usize, flags: crate::memory::Flags) -> bool {
        todo!()
    }

    unsafe fn unmap(vm_addr: usize) {
        todo!()
    }

    fn vm_to_phy(vm_addr: usize) -> Option<usize> {
        todo!()
    }
}
