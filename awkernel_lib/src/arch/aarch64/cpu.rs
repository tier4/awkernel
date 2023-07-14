use crate::cpu::CPU;
use awkernel_aarch64::mpidr_el1;

pub(crate) struct ArchCPU;

impl CPU for ArchCPU {
    fn cpu_id() -> usize {
        let mpidr = mpidr_el1::get();
        mpidr as usize & 0xFF
    }
}
