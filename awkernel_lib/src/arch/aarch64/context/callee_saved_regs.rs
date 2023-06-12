//! `save_context` and `restore_context` are specified by `specification/awkernel_lib/src/arch/aarch64/context.rs/callee_saved_regs`.
//! If you update these functions, please update the specification and verify them.
use core::arch::global_asm;

#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct Context {
    // 8 * 8 bytes
    pub fp_regs: FPRegs,

    //------------------------------ offset: 16 * 4 (+4)

    // 8 * 12 bytes
    pub gp_regs: GPRegs,

    // ----------------------------- offset: 16 * 10 (+6)

    // 8 * 2 bytes
    pub sp: u64, // stack pointer
    _unused: [u8; 8],
}

/// Callee saved general purpose registers.
#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct GPRegs {
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

/// Callee saved floating-point registers.
#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct FPRegs {
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
.global context_switch
context_switch:
// Save the current context.

// Store floating-point registers.
stp      d8,  d9, [x0], #16
stp     d10, d11, [x0], #16
stp     d12, d13, [x0], #16
stp     d14, d15, [x0], #16

// Store general purpose registers.
stp     x19, x20, [x0], #16
stp     x21, x22, [x0], #16
stp     x23, x24, [x0], #16
stp     x25, x26, [x0], #16
stp     x27, x28, [x0], #16
stp     x29, x30, [x0], #16

// Store SP.
mov     x9, sp
str     x9, [x0]


// Restore the next context.

// Load floating-point registers.
ldp      d8,  d9, [x1], #16
ldp     d10, d11, [x1], #16
ldp     d12, d13, [x1], #16
ldp     d14, d15, [x1], #16

// Load general purpose registers.
ldp     x19, x20, [x1], #16
ldp     x21, x22, [x1], #16
ldp     x23, x24, [x1], #16
ldp     x25, x26, [x1], #16
ldp     x27, x28, [x1], #16
ldp     x29, x30, [x1], #16

// Load SP.
ldr     x9, [x1]
mov     sp, x9

ret
"
);

extern "C" {
    pub fn save_context(ptr: *mut Context) -> u64;
    pub fn restore_context(ptr: *const Context);
}

impl crate::context::Context for Context {
    unsafe fn set_stack_pointer(&mut self, sp: usize) {
        self.sp = sp as u64;
    }

    unsafe fn set_entry_point(&mut self, entry: extern "C" fn(usize) -> !, arg: usize) {
        self.gp_regs.x19 = arg as u64;
        self.gp_regs.x20 = entry as u64;
        self.gp_regs.x30 = entry_point as *const () as u64;
    }

    unsafe fn set_argument(&mut self, arg: usize) {
        self.gp_regs.x19 = arg as u64;
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
