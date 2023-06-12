#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct Context {
    // 8 * 64 bytes
    pub fp_regs: FPRegs,

    // 8 * 2 bytes ---------- offset: 16 * 32
    pub fp_fpsr: u64,
    pub fp_fpcr: u64,

    // 8 * 19 bytes --------- offset: 16 * 33 (+1)
    pub gp_regs: GPRegs,

    // 8 bytes
    pub elr: u64, // exception link register,

    // 8 * 2 bytes ---------- offset: 16 * 43 (+10)
    pub spsr: u32, // saved program status register
    _unused: [u8; 4],
    pub sp: u64, // stack pointer
}

/// General Purpose Registers.
#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct GPRegs {
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
    pub x30: u64, // link register
}

/// Floating Point Registers.
#[derive(Debug, Copy, Clone, Default)]
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
