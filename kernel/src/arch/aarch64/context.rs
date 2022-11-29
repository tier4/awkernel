use core::arch::asm;

extern "C" {
    fn save_context(ptr: *const GpRegs) -> usize;
}

/// General Purpose Registers
#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct GpRegs {
    pub x0: u64,
    pub x1: u64,
    pub x2: u64,
    pub x3: u64,
    pub x4: u64,
    pub x5: u64,
    pub x6: u64,
    pub x7: u64,
    pub x8: u64,
    pub x9: u64,
    pub x10: u64,
    pub x11: u64,
    pub x12: u64,
    pub x13: u64,
    pub x14: u64,
    pub x15: u64,
    pub x16: u64,
    pub x17: u64,
    pub x18: u64,
    pub x19: u64,
    pub x20: u64,
    pub x21: u64,
    pub x22: u64,
    pub x23: u64,
    pub x24: u64,
    pub x25: u64,
    pub x26: u64,
    pub x27: u64,
    pub x28: u64,
    pub x29: u64,
    pub x30: u64,  // link register
    pub elr: u64,  // exception link register
    pub spsr: u32, // saved program status register
    _unused: [u8; 4],
    pub sp: u64, // stack pointer
}

impl GpRegs {
    pub const fn new() -> GpRegs {
        GpRegs {
            x0: 0,
            x1: 0,
            x2: 0,
            x3: 0,
            x4: 0,
            x5: 0,
            x6: 0,
            x7: 0,
            x8: 0,
            x9: 0,
            x10: 0,
            x11: 0,
            x12: 0,
            x13: 0,
            x14: 0,
            x15: 0,
            x16: 0,
            x17: 0,
            x18: 0,
            x19: 0,
            x20: 0,
            x21: 0,
            x22: 0,
            x23: 0,
            x24: 0,
            x25: 0,
            x26: 0,
            x27: 0,
            x28: 0,
            x29: 0,
            x30: 0,
            elr: 0,
            spsr: 0,
            _unused: [0; 4],
            sp: 0,
        }
    }

    pub fn context_switch(&self) -> ! {
        unsafe {
            asm! {
                "mov     x0, {}

                 ldp     lr,  x2,  [x0, #16 * 15]
                 ldr     w3,       [x0, #16 * 16]
                 ldr     x4,       [x0, #16 * 16 + 8]

                 msr     elr_el1, x2
                 msr     spsr_el1, x3
                 mov     sp, x4

                 ldp     x2,  x3,  [x0, #16 * 1]
                 ldp     x4,  x5,  [x0, #16 * 2]
                 ldp     x6,  x7,  [x0, #16 * 3]
                 ldp     x8,  x9,  [x0, #16 * 4]
                 ldp     x10, x11, [x0, #16 * 5]
                 ldp     x12, x13, [x0, #16 * 6]
                 ldp     x14, x15, [x0, #16 * 7]
                 ldp     x16, x17, [x0, #16 * 8]
                 ldp     x18, x19, [x0, #16 * 9]
                 ldp     x20, x21, [x0, #16 * 10]
                 ldp     x22, x23, [x0, #16 * 11]
                 ldp     x24, x25, [x0, #16 * 12]
                 ldp     x26, x27, [x0, #16 * 13]
                 ldp     x28, x29, [x0, #16 * 14]

                 ldp     x0,  x1,  [x0, #16 * 0]

                 ret",
                in(reg) self as *const GpRegs
            }
        }

        unreachable!()
    }

    /// Return 0 if context is saved.
    /// Return 1 if context switching is performed.
    pub fn save_context(&mut self) -> usize {
        unsafe { save_context(self as *const GpRegs) }
    }
}

/// System Registers of EL1 and EL0
#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct EL1SysRegs {
    pub sctlr_el1: u64,
    pub actlr_el1: u64,
    pub cpacr_el1: u64,
    pub csselr_el1: u64,
    pub sp_el1: u64,
    pub esr_el1: u64,
    pub ttbr0_el1: u64,
    pub ttbr1_el1: u64,
    pub mair_el1: u64,
    pub amair_el1: u64,
    pub tcr_el1: u64,
    pub tpidr_el1: u64,
    pub tpidr_el0: u64,
    pub tpidrro_el0: u64,
    pub par_el1: u64,
    pub far_el1: u64,
    pub afsr0_el1: u64,
    pub afsr1_el1: u64,
    pub contextidr_el1: u64,
    pub vbar_el1: u64,
    // If the platform is AArch64-only, there is no need to save and restore these
    // AArch32 registers.
    // spsr_abt: u64,
    // spsr_udt: u64,
    // spsr_irq: u64,
    // spsr_fiq: u64,
    // dacr32_el2: u64,
    // ifsr32_el2: u64,
    // If the timer registers aren't saved and restored, we don't have to reserve
    // space for them in the context
    pub cntp_ctl_el0: u64,
    pub cntp_cval_el0: u64,
    pub cntv_ctl_el0: u64,
    pub cntv_cval_el0: u64,
    pub cntkctl_el1: u64,
    // MTE regs (from Armv 8.5)
    // tfsr0_el1: u64,
    // tfsr_el1: u64,
    // rgsr_el1: u64,
    // gcr_el1: u64,
}

impl EL1SysRegs {
    pub const fn new() -> EL1SysRegs {
        EL1SysRegs {
            sctlr_el1: 0,
            actlr_el1: 0,
            cpacr_el1: 0,
            csselr_el1: 0,
            sp_el1: 0,
            esr_el1: 0,
            ttbr0_el1: 0,
            ttbr1_el1: 0,
            mair_el1: 0,
            amair_el1: 0,
            tcr_el1: 0,
            tpidr_el1: 0,
            tpidr_el0: 0,
            tpidrro_el0: 0,
            par_el1: 0,
            far_el1: 0,
            afsr0_el1: 0,
            afsr1_el1: 0,
            contextidr_el1: 0,
            vbar_el1: 0,
            cntp_ctl_el0: 0,
            cntp_cval_el0: 0,
            cntv_ctl_el0: 0,
            cntv_cval_el0: 0,
            cntkctl_el1: 0,
        }
    }
}

/// Floating Point Registers
#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct FPRegs {
    fp_q0: [u8; 16],
    fp_q1: [u8; 16],
    fp_q2: [u8; 16],
    fp_q3: [u8; 16],
    fp_q4: [u8; 16],
    fp_q5: [u8; 16],
    fp_q6: [u8; 16],
    fp_q7: [u8; 16],
    fp_q8: [u8; 16],
    fp_q9: [u8; 16],
    fp_q10: [u8; 16],
    fp_q11: [u8; 16],
    fp_q12: [u8; 16],
    fp_q13: [u8; 16],
    fp_q14: [u8; 16],
    fp_q15: [u8; 16],
    fp_q16: [u8; 16],
    fp_q17: [u8; 16],
    fp_q18: [u8; 16],
    fp_q19: [u8; 16],
    fp_q20: [u8; 16],
    fp_q21: [u8; 16],
    fp_q22: [u8; 16],
    fp_q23: [u8; 16],
    fp_q24: [u8; 16],
    fp_q25: [u8; 16],
    fp_q26: [u8; 16],
    fp_q27: [u8; 16],
    fp_q28: [u8; 16],
    fp_q29: [u8; 16],
    fp_q30: [u8; 16],
    fp_q31: [u8; 16],
    // for AArch32
    // fpexc32_el2: [u8; 16],
    fp_fpsr: u64,
    fp_fpcr: u64,
}

impl FPRegs {
    pub const fn new() -> FPRegs {
        FPRegs {
            fp_q0: [0; 16],
            fp_q1: [0; 16],
            fp_q2: [0; 16],
            fp_q3: [0; 16],
            fp_q4: [0; 16],
            fp_q5: [0; 16],
            fp_q6: [0; 16],
            fp_q7: [0; 16],
            fp_q8: [0; 16],
            fp_q9: [0; 16],
            fp_q10: [0; 16],
            fp_q11: [0; 16],
            fp_q12: [0; 16],
            fp_q13: [0; 16],
            fp_q14: [0; 16],
            fp_q15: [0; 16],
            fp_q16: [0; 16],
            fp_q17: [0; 16],
            fp_q18: [0; 16],
            fp_q19: [0; 16],
            fp_q20: [0; 16],
            fp_q21: [0; 16],
            fp_q22: [0; 16],
            fp_q23: [0; 16],
            fp_q24: [0; 16],
            fp_q25: [0; 16],
            fp_q26: [0; 16],
            fp_q27: [0; 16],
            fp_q28: [0; 16],
            fp_q29: [0; 16],
            fp_q30: [0; 16],
            fp_q31: [0; 16],
            fp_fpsr: 0,
            fp_fpcr: 0,
        }
    }
}
