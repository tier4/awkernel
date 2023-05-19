#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct Context {
    // 8 * 64 bytes
    pub fp_regs: FPRegs,

    // 8 * 2 bytes ---------- offset: 16 * 32
    pub fp_fpsr: u64,
    pub fp_fpcr: u64,

    // 8 * 31 bytes --------- offset: 16 * 33 (+1)
    pub gp_regs: GpRegs,

    // 8 bytes
    pub elr: u64, // exception link register,

    // ---------------------- offset: 16 * 49 (+16)

    // 8 * 2 bytes
    pub spsr: u32, // saved program status register
    _unused: [u8; 4],
    pub sp: u64, // stack pointer
}

/// General Purpose Registers.
#[derive(Debug, Copy, Clone, Default)]
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

core::arch::global_asm!(
    "
save_context:
// Store floating-point registers.
str      q0, [x0], #16
str      q1, [x0], #16
str      q2, [x0], #16
str      q3, [x0], #16
str      q4, [x0], #16
str      q5, [x0], #16
str      q6, [x0], #16
str      q7, [x0], #16
str      q8, [x0], #16
str      q9, [x0], #16
str     q10, [x0], #16
str     q11, [x0], #16
str     q12, [x0], #16
str     q13, [x0], #16
str     q14, [x0], #16
str     q15, [x0], #16
str     q16, [x0], #16
str     q17, [x0], #16
str     q18, [x0], #16
str     q19, [x0], #16
str     q20, [x0], #16
str     q21, [x0], #16
str     q22, [x0], #16
str     q23, [x0], #16
str     q24, [x0], #16
str     q25, [x0], #16
str     q26, [x0], #16
str     q27, [x0], #16
str     q28, [x0], #16
str     q29, [x0], #16
str     q30, [x0], #16
str     q31, [x0], #16

// Store general purpose registers.
stp      x2,  x3, [x0, #16 * 2]
stp      x4,  x5, [x0, #16 * 3]
stp      x6,  x7, [x0, #16 * 4]
stp      x8,  x9, [x0, #16 * 5]
stp     x10, x11, [x0, #16 * 6]
stp     x12, x13, [x0, #16 * 7]
stp     x14, x15, [x0, #16 * 8]
stp     x16, x17, [x0, #16 * 9]
stp     x18, x19, [x0, #16 * 10]
stp     x20, x21, [x0, #16 * 11]
stp     x22, x23, [x0, #16 * 12]
stp     x24, x25, [x0, #16 * 13]
stp     x26, x27, [x0, #16 * 14]
stp     x28, x29, [x0, #16 * 15]
str     x30, [x0, #16 * 16]

// Store FPSR and FPCR registers.
mrs     x9, fpsr
mrs     x10, fpcr
stp     x9, x10, [x0]

// Store SPSR.
add     x0, x0, #16 * 17
mrs     x9, spsr_el1
str     w9, [x0]

// Store SP.
mov     x9, sp
str     x9, [x0, #8]

// Store x0 and x1.
sub     x9, x0, #16 * 16
sub     x0, x0, #16 * 49
stp     x0, x1, [x9]

ret


restore_context:
// Load floating-point registers.
ldr      q0, [x0], #16
ldr      q1, [x0], #16
ldr      q2, [x0], #16
ldr      q3, [x0], #16
ldr      q4, [x0], #16
ldr      q5, [x0], #16
ldr      q6, [x0], #16
ldr      q7, [x0], #16
ldr      q8, [x0], #16
ldr      q9, [x0], #16
ldr     q10, [x0], #16
ldr     q11, [x0], #16
ldr     q12, [x0], #16
ldr     q13, [x0], #16
ldr     q14, [x0], #16
ldr     q15, [x0], #16
ldr     q16, [x0], #16
ldr     q17, [x0], #16
ldr     q18, [x0], #16
ldr     q19, [x0], #16
ldr     q20, [x0], #16
ldr     q21, [x0], #16
ldr     q22, [x0], #16
ldr     q23, [x0], #16
ldr     q24, [x0], #16
ldr     q25, [x0], #16
ldr     q26, [x0], #16
ldr     q27, [x0], #16
ldr     q28, [x0], #16
ldr     q29, [x0], #16
ldr     q30, [x0], #16
ldr     q31, [x0], #16

// Load general purpose registers.
ldp      x4,  x5, [x0, #16 * 3]
ldp      x6,  x7, [x0, #16 * 4]
ldp      x8,  x9, [x0, #16 * 5]
ldp     x10, x11, [x0, #16 * 6]
ldp     x12, x13, [x0, #16 * 7]
ldp     x14, x15, [x0, #16 * 8]
ldp     x16, x17, [x0, #16 * 9]
ldp     x18, x19, [x0, #16 * 10]
ldp     x20, x21, [x0, #16 * 11]
ldp     x22, x23, [x0, #16 * 12]
ldp     x24, x25, [x0, #16 * 13]
ldp     x26, x27, [x0, #16 * 14]
ldp     x28, x29, [x0, #16 * 15]
ldr     x30, [x0, #16 * 16]

// Load FPSR and FPCR registers.
ldp     x2, x3, [x0]
msr     fpsr, x2
msr     fpcr, x3

// Load SPSR.
add     x0, x0, #16 * 17
ldr     w1, [x0]
msr     spsr_el1, x1

// Load SP.
ldr     x2, [x0, #8]
mov     sp, x2

// ELR == 0?
ldr     x2, [x0, #-8]
sub     x0, x0, #16 * 16
cbz     x2, 1f

// Load ELR
msr     elr_el1, x2

// Load x0 to x2.
ldp     x2, x3, [x0, #16]
ldp     x0, x1, [x0]

eret

1:
// Load x0 to x2.
ldp     x2, x3, [x0, #16]
ldp     x0, x1, [x0]

ret
"
);

extern "C" {
    fn save_context(ptr: *mut Context);
    fn restore_context(ptr: *const Context);
}

impl crate::context::Context for Context {
    fn set_jump(&mut self) {
        self.elr = 0;
        let ptr = self as *mut _;
        unsafe { save_context(ptr) };
    }

    fn long_jump(&self) -> ! {
        unsafe { restore_context(self as *const _) };
        unreachable!()
    }
}
