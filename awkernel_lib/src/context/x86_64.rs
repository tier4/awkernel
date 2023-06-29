//! The x86_64 System V ABI.

#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct Context {
    _todo: usize,
}

core::arch::global_asm!(
    "
.global context_switch
context_switch:
    jmp context_switch
"
);

impl crate::context::Context for Context {
    unsafe fn set_stack_pointer(&mut self, sp: usize) {
        todo!();
    }

    unsafe fn set_entry_point(&mut self, entry: extern "C" fn(usize) -> !, arg: usize) {
        todo!();
    }

    unsafe fn set_argument(&mut self, arg: usize) {
        todo!();
    }
}
