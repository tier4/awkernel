use crate::sync::mcs::MCSNode;

#[cfg(feature = "rv32")]
use super::rv32::RV32 as ArchImpl;
#[cfg(feature = "rv64")]
use super::rv64::RV64 as ArchImpl;

pub(super) mod address;
pub mod barrier;
pub mod clint;
pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod frame_allocator;
pub(super) mod interrupt;
pub mod interrupt_controller;
pub(super) mod page_table;
pub(super) mod paging;
pub(super) mod vm;

pub fn init_page_allocator() {
    frame_allocator::init_page_allocator();
}

pub fn init_kernel_space() {
    vm::init_kernel_space();
}

pub fn activate_kernel_space() {
    vm::activate_kernel_space();
}

pub fn kernel_token() -> usize {
    vm::kernel_token()
}

pub fn translate_kernel_address(vpn: address::VirtPageNum) -> Option<page_table::PageTableEntry> {
    let mut node = MCSNode::new();
    let mut kernel_space = vm::KERNEL_SPACE.lock(&mut node);
    if let Some(ref mut space) = *kernel_space {
        space.translate(vpn)
    } else {
        None
    }
}
