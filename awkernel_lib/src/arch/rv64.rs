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
