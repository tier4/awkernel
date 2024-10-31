pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod dvfs;
pub(super) mod interrupt;
pub(super) mod paging;

pub struct RV64;

impl super::Arch for RV64 {}
