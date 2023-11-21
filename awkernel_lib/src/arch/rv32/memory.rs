use crate::page_table::{Flags, PageTable};

/// We should set memory end based on specific device
pub const MEMORY_END: u64 = 0x88000000;
pub struct Memory {
    page_table: PageTable,
    area: Vec<MapArea>,
}

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
