use crate::pcie::PCIeInfo;
use alloc::boxed::Box;

#[derive(Debug)]
pub struct VirtioCap {
    _cap_ptr: usize,
    next_virtio_cap: Option<Box<VirtioCap>>,
}

impl VirtioCap {
    pub fn new(_info: &PCIeInfo, cap_ptr: usize) -> Self {
        Self {
            _cap_ptr: cap_ptr,
            next_virtio_cap: None,
        }
    }

    pub fn set_next_virtio_cap(&mut self, next_virtio_cap: Option<Box<VirtioCap>>) {
        self.next_virtio_cap = next_virtio_cap;
    }
}
