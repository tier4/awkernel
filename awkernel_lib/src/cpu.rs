use crate::arch::ArchCPU;

pub const NUM_MAX_CPU: usize = 512;

pub trait CPU {
    fn cpu_id() -> usize;
    // fn notify(id: usize);
}

pub fn cpu_id() -> usize {
    ArchCPU::cpu_id()
}
