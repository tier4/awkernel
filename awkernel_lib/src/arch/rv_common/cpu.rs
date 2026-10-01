use super::ArchImpl;
use crate::cpu::CPU;
use riscv::register::mhartid;

impl CPU for ArchImpl {
    #[inline(always)]
    fn cpu_id() -> usize {
        mhartid::read()
    }

    #[inline(always)]
    fn raw_cpu_id() -> usize {
        Self::cpu_id()
    }
}
