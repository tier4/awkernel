use crate::cpu::CPU;

impl CPU for super::RV32 {
    fn cpu_id() -> usize {
        let hartid: usize;
        unsafe {
            core::arch::asm!("csrr {}, mhartid", out(reg) hartid);
        }
        hartid
    }

    fn raw_cpu_id() -> usize {
        Self::cpu_id()
    }
}
