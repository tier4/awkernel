#[derive(Debug, Copy, Clone, Default)]
pub struct Context;

impl crate::context::Context for Context {
    fn set_jump(&mut self) -> bool {
        todo!();
    }

    unsafe fn long_jump(&self) -> ! {
        todo!();
    }

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
