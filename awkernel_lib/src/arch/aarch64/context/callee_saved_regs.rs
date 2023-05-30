//! `save_context` and `restore_context` are specified by `specification/awkernel_lib/src/arch/aarch64/context.rs/callee_saved_regs`.
//! If you update these functions, please update the specification and verify them.
use core::arch::global_asm;

#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct CalleeSavedContext {
    // 8 * 8 bytes
    pub fp_regs: CalleeSavedFPRegs,

    //------------------------------ offset: 16 * 4

    // 8 * 2 bytes
    pub fp_fpsr: u64,
    pub fp_fpcr: u64,

    //------------------------------ offset: 16 * 5 (+1)

    // 8 * 11 bytes
    pub gp_regs: CalleeSavedGpRegs,

    pub sp: u64, // stack pointer

    // ----------------------------- offset: 16 * 11 (+6)

    // 8 * 2 bytes
    pub spsr: u32, // saved program status register
    _unused: [u8; 12],
}

/// Callee saved general purpose registers.
#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct CalleeSavedGpRegs {
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
    pub x30: u64, // link register
}

/// Callee saved floating-point registers.
#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct CalleeSavedFPRegs {
    v8: u64,
    v9: u64,
    v10: u64,
    v11: u64,
    v12: u64,
    v13: u64,
    v14: u64,
    v15: u64,
}

core::arch::global_asm!(
    "
.global save_context
save_context:
// Store floating-point registers.
stp      d8,  d9, [x0], #16
stp     d10, d11, [x0], #16
stp     d12, d13, [x0], #16
stp     d14, d15, [x0], #16

// Store general purpose registers.
stp     x19, x20, [x0, #16 * 1]
stp     x21, x22, [x0, #16 * 2]
stp     x23, x24, [x0, #16 * 3]
stp     x25, x26, [x0, #16 * 4]
stp     x27, x28, [x0, #16 * 5]
str     x30, [x0, #16 * 6]

// Store FPSR and FPCR registers.
mrs     x9, fpsr
mrs     x10, fpcr
stp     x9, x10, [x0]

// Store SPSR.
add     x0, x0, #16 * 7
mrs     x11, spsr_el1
str     w11, [x0]

// Store SP.
mov     x12, sp
str     x12, [x0, #-8]

mov     x0, #1

ret


restore_context:
// Load floating-point registers.
ldp      d8,  d9, [x0], #16
ldp     d10, d11, [x0], #16
ldp     d12, d13, [x0], #16
ldp     d14, d15, [x0], #16

// Load general purpose registers.
ldp     x19, x20, [x0, #16 * 1]
ldp     x21, x22, [x0, #16 * 2]
ldp     x23, x24, [x0, #16 * 3]
ldp     x25, x26, [x0, #16 * 4]
ldp     x27, x28, [x0, #16 * 5]
ldr     x30, [x0, #16 * 6]

// Load FPSR and FPCR registers.
ldp     x9, x10, [x0]
msr     fpsr, x9
msr     fpcr, x10

// Load SPSR.
add     x0, x0, #16 * 7
ldr     w11, [x0]
msr     spsr_el1, x11

// Load SP.
ldr     x12, [x0, #-8]
mov     sp, x12

mov     x0, #0

ret
"
);

extern "C" {
    pub fn save_context(ptr: *mut CalleeSavedContext) -> u64;
    pub fn restore_context(ptr: *const CalleeSavedContext);
}

impl crate::context::Context for CalleeSavedContext {
    #[inline(always)]
    fn set_jump(&mut self) -> bool {
        let ptr = self as *mut _;
        let val = unsafe { save_context(ptr) };
        val == 0
    }

    unsafe fn long_jump(&self) -> ! {
        unsafe { restore_context(self as *const _) };
        unreachable!()
    }

    unsafe fn set_stack_pointer(&mut self, sp: usize) {
        self.sp = sp as u64;
    }

    unsafe fn set_entry_point(&mut self, entry: extern "C" fn(usize) -> !, arg: usize) {
        log::debug!("entry = 0x{:x}", entry as *const () as u64);

        self.gp_regs.x19 = arg as u64;
        self.gp_regs.x20 = entry as u64;
        self.gp_regs.x30 = entry_point as *const () as u64;
    }
}

extern "C" {
    fn entry_point() -> !;
}

global_asm!(
    "
entry_point:
   mov     x0, x19
   blr     x20
1:
    wfi
    b       1b
"
);
