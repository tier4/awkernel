use crate::cpu::CPU;

pub(crate) struct ArchCPU;

impl CPU for ArchCPU {
    fn cpu_id() -> usize {
        let hartid: usize;
        unsafe {
            core::arch::asm!("csrr {}, mhartid", out(reg) hartid);
        }
        hartid
    }
}
