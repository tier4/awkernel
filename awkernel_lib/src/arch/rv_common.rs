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
pub mod plic;
pub(super) mod power;
pub(super) mod vm;

/// Initialise the frame allocator over `[start, end)`.
/// This range must be reserved exclusively for page table frames —
/// it must not overlap with the heap region passed to `init_kernel_space`.
pub fn init_page_allocator(start: usize, end: usize) {
    frame_allocator::init_page_allocator(start, end);
}

/// Build the kernel page table and identity-map the page-table-frame region
/// `[pt_start, heap_start)` and the heap region `[heap_start, memory_end)`.
/// Must be called after `init_page_allocator` and after the global heap is initialised.
pub fn init_kernel_space(pt_start: usize, heap_start: usize, memory_end: usize) {
    vm::init_kernel_space(pt_start, heap_start, memory_end);
}

pub fn activate_kernel_space() {
    vm::activate_kernel_space();
}

pub fn kernel_token() -> usize {
    vm::kernel_token()
}

pub fn get_heap_size() -> usize {
    vm::get_heap_size()
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
