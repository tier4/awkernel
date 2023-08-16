//! The x86_64 System V ABI.
use core::arch::global_asm;

#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct Context {
    pub rbx: u64,
    pub rsp: u64,
    pub rbp: u64,
    pub r12: u64,
    pub r13: u64,
    pub r14: u64,
    pub r15: u64,
}

core::arch::global_asm!(
    "
.global context_switch
context_switch:
// Store general purpose registers
mov   [rdi], rbx
mov  8[rdi], rsp
mov 16[rdi], rbp
mov 24[rdi], r12
mov 32[rdi], r13
mov 40[rdi], r14
mov 48[rdi], r15

// Load general purpose registers
mov rbx,   [rsi]
mov rsp,  8[rsi]
mov rbp, 16[rsi]
mov r12, 24[rsi]
mov r13, 32[rsi]
mov r14, 40[rsi]
mov r15, 48[rsi]

ret
"
);

impl crate::context::Context for Context {
    unsafe fn set_stack_pointer(&mut self, sp: usize) {
        self.rsp = sp as u64;
    }

    unsafe fn set_entry_point(&mut self, entry: extern "C" fn(usize) -> !, arg: usize) {
        self.r12 = arg as u64;
        self.r13 = entry as usize as u64;

        let entry_point_addr = entry_point as usize as u64;

        unsafe {
            core::arch::asm!("mov {}, rsp", lateout(reg) self.r15);
            core::arch::asm!("mov rsp, {}", in(reg) self.rsp);
            core::arch::asm!("push {}", in(reg) entry_point_addr);
            core::arch::asm!("mov rsp, {}", in(reg) self.r15);
        }

        self.rsp -= 8;
    }

    unsafe fn set_argument(&mut self, arg: usize) {
        self.r12 = arg as u64;
    }
}

extern "C" {
    fn entry_point() -> !;
}

global_asm!(
    "
entry_point:
    mov  rdi, r12
    call r13
1:
    hlt
    jmp  1b
"
);