# Context Switch

`Context` defined in [awkernel_lib/src/context.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/context.rs)
is a trait that enables preemptive multitasking.
It provides methods to set the stack pointer, entry point,
and argument of the context as follows.

```rust
pub trait Context: Default {
    /// # Safety
    ///
    /// Ensure that changing the stack pointer is valid at that time.
    unsafe fn set_stack_pointer(&mut self, sp: usize);

    /// # Safety
    ///
    /// This function must be called for only initialization purpose.
    unsafe fn set_entry_point(&mut self, entry: extern "C" fn(usize) -> !, arg: usize);

    /// # Safety
    ///
    /// This function must be called for only initialization purpose.
    unsafe fn set_argument(&mut self, arg: usize);
}
```

The `context_switch` function must be implemented for each architecture
to enable context switching.

```rust
extern "C" {
    /// Switch context from `current` to `next`.
    pub fn context_switch(current: *mut ArchContext, next: *const ArchContext);
}
```

The `context_switch` function stores and restores CPU registers,
and the `ArchContext` structure is an architecture-specific context structure.

# Disable Preemption

In [awkernel_async_lib/Cargo.toml](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/Cargo.toml), there is the `no_preempt` feature to disable preemption.

```toml
[features]
default = []
std = ["awkernel_lib/std", "no_preempt"]
no_preempt = []
```

If you want to disable preemption, please enable the `no_preempt` feature as
`default = ["no_preempt"]`.

# Implementation

## x86_64

For x86_64, the `Context` structure is defined in
[awkernel_lib/src/context/x86_64.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/context/x86_64.rs) as follows.

```rust
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
```

The `Context` structure is imported as the `ArchContext` in [awkernel_lib/src/context.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/context.rs).

The `context_switch` function is implemented in assembly as follows.
This stores and restores only general-purpose registers because
the floating-point registers are stored and restored by each interrupt handler.

```rust
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
```

The [`Context`:awkernel_lib/src/context.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/context.rs) trait is implemented for the [`Context`:awkernel_lib/src/context/x86_64.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/context/x86_64.rs) structure as follows.
These methods set the stack pointer, entry point, and argument of the context.

```rust
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
.global entry_point
entry_point:
    mov  rdi, r12
    call r13
1:
    hlt
    jmp  1b
"
);
```

## AArch64

For AArch64, the `Context` structure is defined in
[awkernel_lib/src/context/aarch64.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/context/aarch64.rs) as follows.

```rust
#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct Context {
    // 8 * 8 bytes
    pub fp_regs: FPRegs, // floating point registers

    //------------------------------ offset: 16 * 4 (+4)

    // 8 * 12 bytes
    pub gp_regs: GPRegs, // general purpose registers

    // ----------------------------- offset: 16 * 10 (+6)

    // 8 * 2 bytes
    pub sp: u64, // stack pointer
    _unused: [u8; 8],
}
```

The `Context` structure is imported as the `ArchContext` in [awkernel_lib/src/context.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/context.rs).


The `context_switch` function is implemented in assembly as follows.

```rust
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
```

The [`Context`:awkernel_lib/src/context.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/context.rs) trait is implemented for the [`Context`:awkernel_lib/src/context/aarch64.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/context/aarch64.rs) structure as follows.
These methods set the stack pointer, entry point, and argument of the context.

```rust
impl crate::context::Context for Context {
    unsafe fn set_stack_pointer(&mut self, sp: usize) {
        self.sp = sp as u64;
    }

    unsafe fn set_entry_point(&mut self, entry: extern "C" fn(usize) -> !, arg: usize) {
        self.gp_regs.x19 = arg as u64;
        self.gp_regs.x20 = entry as usize as u64;
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
.global entry_point
entry_point:
    mov     x0, x19
    blr     x20
1:
    wfi
    b       1b
"
);
```
