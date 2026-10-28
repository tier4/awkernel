//! The RISC-V LP64D calling convention.
//!
//! `context_switch` is specified by `specification/awkernel_lib/src/context/rv64`.
//! If you update this function, please update the specification and verify it.
use core::arch::global_asm;

#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct Context {
    // 8 * 14 bytes
    pub gp_regs: GPRegs,

    //------------------------------ offset: 8 * 14

    // 8 * 12 bytes
    pub fp_regs: FPRegs,
}

/// Callee saved general purpose registers.
#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct GPRegs {
    pub ra: u64, // return address
    pub sp: u64, // stack pointer
    pub s0: u64, // frame pointer
    pub s1: u64,
    pub s2: u64,
    pub s3: u64,
    pub s4: u64,
    pub s5: u64,
    pub s6: u64,
    pub s7: u64,
    pub s8: u64,
    pub s9: u64,
    pub s10: u64,
    pub s11: u64,
}

/// Callee saved floating-point registers.
#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct FPRegs {
    fs0: u64,
    fs1: u64,
    fs2: u64,
    fs3: u64,
    fs4: u64,
    fs5: u64,
    fs6: u64,
    fs7: u64,
    fs8: u64,
    fs9: u64,
    fs10: u64,
    fs11: u64,
}

global_asm!(
    "
// `global_asm!` is assembled without the target features, so enable D explicitly.
.option push
.option arch, +d

.global context_switch
context_switch:
// Save the current context.

// Store general purpose registers.
sd       ra,   0(a0)
sd       sp,   8(a0)
sd       s0,  16(a0)
sd       s1,  24(a0)
sd       s2,  32(a0)
sd       s3,  40(a0)
sd       s4,  48(a0)
sd       s5,  56(a0)
sd       s6,  64(a0)
sd       s7,  72(a0)
sd       s8,  80(a0)
sd       s9,  88(a0)
sd      s10,  96(a0)
sd      s11, 104(a0)

// Store floating-point registers.
fsd     fs0, 112(a0)
fsd     fs1, 120(a0)
fsd     fs2, 128(a0)
fsd     fs3, 136(a0)
fsd     fs4, 144(a0)
fsd     fs5, 152(a0)
fsd     fs6, 160(a0)
fsd     fs7, 168(a0)
fsd     fs8, 176(a0)
fsd     fs9, 184(a0)
fsd    fs10, 192(a0)
fsd    fs11, 200(a0)


// Restore the next context.

// Load general purpose registers.
ld       ra,   0(a1)
ld       sp,   8(a1)
ld       s0,  16(a1)
ld       s1,  24(a1)
ld       s2,  32(a1)
ld       s3,  40(a1)
ld       s4,  48(a1)
ld       s5,  56(a1)
ld       s6,  64(a1)
ld       s7,  72(a1)
ld       s8,  80(a1)
ld       s9,  88(a1)
ld      s10,  96(a1)
ld      s11, 104(a1)

// Load floating-point registers.
fld     fs0, 112(a1)
fld     fs1, 120(a1)
fld     fs2, 128(a1)
fld     fs3, 136(a1)
fld     fs4, 144(a1)
fld     fs5, 152(a1)
fld     fs6, 160(a1)
fld     fs7, 168(a1)
fld     fs8, 176(a1)
fld     fs9, 184(a1)
fld    fs10, 192(a1)
fld    fs11, 200(a1)

ret

.option pop
"
);

impl crate::context::Context for Context {
    unsafe fn set_stack_pointer(&mut self, sp: usize) {
        self.gp_regs.sp = sp as u64;
    }

    unsafe fn set_entry_point(&mut self, entry: extern "C" fn(usize) -> !, arg: usize) {
        self.gp_regs.s0 = arg as u64;
        self.gp_regs.s1 = entry as usize as u64;
        self.gp_regs.ra = entry_point as *const () as u64;
    }

    unsafe fn set_argument(&mut self, arg: usize) {
        self.gp_regs.s0 = arg as u64;
    }
}

extern "C" {
    fn entry_point() -> !;
}

global_asm!(
    "
.global entry_point
entry_point:
    mv      a0, s0
    jalr    s1
1:
    wfi
    j       1b
"
);
