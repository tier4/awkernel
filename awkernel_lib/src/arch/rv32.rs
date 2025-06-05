pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod dvfs;
pub(super) mod interrupt;
pub(super) mod paging;

// Virtual Memory
pub(super) mod address;
pub(super) mod frame_allocator;
pub(super) mod memory;
pub(super) mod page_table;

pub struct RV32;

impl super::Arch for RV32 {}
