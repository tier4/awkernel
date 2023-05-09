#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct Context {
    // 8 * 31 bytes
    pub gp_regs: GpRegs,

    // 8 * 3 bytes
    pub elr: u64,  // exception link register
    pub spsr: u32, // saved program status register
    _unused: [u8; 4],
    pub sp: u64, // stack pointer

    // 8 * 64 bytes
    pub fp_regs: FPRegs,

    // 8 * 2 bytes
    pub fp_fpsr: u64,
    pub fp_fpcr: u64,
}

/// General Purpose Registers.
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
    pub x30: u64, // link register
}

impl GpRegs {
    pub const fn _new() -> GpRegs {
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
        }
    }
}

/// Floating Point Registers.
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
}

impl FPRegs {
    pub const fn _new() -> FPRegs {
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
        }
    }
}
