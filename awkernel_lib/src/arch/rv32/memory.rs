impl crate::memory::Memory for super::RV32 {
    unsafe fn map(_vm_addr: usize, _phy_addr: usize, _flags: crate::memory::Flags) -> bool {
        todo!()
    }

    unsafe fn unmap(_vm_addr: usize) {
        todo!()
    }

    fn vm_to_phy(_vm_addr: usize) -> Option<usize> {
        todo!()
    }
}
