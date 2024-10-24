pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod interrupt;
pub(super) mod paging;
pub(super) mod address;
pub(super) mod page_table;
pub(super) mod frame_allocator;

pub struct RV64;

impl super::Arch for RV64 {}
