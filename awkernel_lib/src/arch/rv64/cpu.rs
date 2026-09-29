use crate::cpu::CPU;

impl CPU for super::RV64 {
    fn cpu_id() -> usize {
        let hartid: usize;
        unsafe {
            // In M-mode, read from tp register (set during boot)
            // This avoids repeatedly accessing mhartid CSR
            core::arch::asm!("mv {}, tp", out(reg) hartid);
        }
        hartid
    }

    fn raw_cpu_id() -> usize {
        Self::cpu_id()
    }
}
