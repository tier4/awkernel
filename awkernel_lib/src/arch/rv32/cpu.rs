use crate::cpu::CPU;

pub(crate) struct ArchCPU;

impl CPU for ArchCPU {
    fn cpu_id() -> usize {
        todo!()
    }
}
