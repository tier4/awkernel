pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod interrupt;

pub fn init() {
    delay::init();
}

pub fn init_per_thread(cpu_id: usize) {
    cpu::init(cpu_id);
}
