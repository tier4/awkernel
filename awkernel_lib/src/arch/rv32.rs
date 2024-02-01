pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod interrupt;
pub(super) mod paging;

pub struct RV32;

impl super::Arch for RV32 {}
