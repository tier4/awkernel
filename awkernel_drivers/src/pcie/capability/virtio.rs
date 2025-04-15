use crate::pcie::PCIeInfo;

#[derive(Debug)]
pub struct VirtioCap {
    _cap_ptr: usize,
}

impl VirtioCap {
    pub fn new(_info: &PCIeInfo, cap_ptr: usize) -> Self {
        Self { _cap_ptr: cap_ptr }
    }
}
