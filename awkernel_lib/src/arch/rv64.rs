pub(super) mod address;
pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod dvfs;
pub(super) mod frame_allocator;
pub(super) mod interrupt;
pub(super) mod page_table;
pub(super) mod paging;
pub(super) mod vm;

pub struct RV64;

impl super::Arch for RV64 {}

pub fn init_page_allocator() {
    frame_allocator::init_page_allocator();
}

pub fn init_kernel_space() {
    vm::init_kernel_space();
}

pub fn activate_kernel_space() {
    vm::activate_kernel_space();
}

pub fn get_kernel_token() -> usize {
    vm::kernel_token()
}

pub fn translate_kernel_address(vpn: address::VirtPageNum) -> Option<page_table::PageTableEntry> {
    use crate::sync::mcs::MCSNode;
    let mut node = MCSNode::new();
    let mut kernel_space = vm::KERNEL_SPACE.lock(&mut node);
    if let Some(ref mut space) = *kernel_space {
        space.translate(vpn)
    } else {
        None
    }
}
