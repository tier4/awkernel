use crate::arch::ArchCPU;

pub trait CPU {
    fn cpu_id() -> usize;
}

fn cpu_id() -> usize {
    ArchCPU::cpu_id()
}
