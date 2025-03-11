pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod dvfs;
pub(super) mod interrupt;
pub(super) mod ntp;

pub fn init() {
    delay::init();
}

pub fn init_per_thread(cpu_id: usize) {
    cpu::init(cpu_id);
}

pub struct StdCommon;

impl super::Arch for StdCommon {}
