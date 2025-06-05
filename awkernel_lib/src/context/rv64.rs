#[derive(Debug, Copy, Clone, Default)]
#[repr(C)]
pub struct Context {
    _todo: usize,
}

core::arch::global_asm!(
    "
.global context_switch
context_switch:
    j context_switch
"
);

impl crate::context::Context for Context {
    unsafe fn set_stack_pointer(&mut self, _sp: usize) {
        todo!();
    }

    unsafe fn set_entry_point(&mut self, _entry: extern "C" fn(usize) -> !, _arg: usize) {
        todo!();
    }

    unsafe fn set_argument(&mut self, _arg: usize) {
        todo!();
    }
}
