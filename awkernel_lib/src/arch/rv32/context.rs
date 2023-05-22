#[derive(Debug, Copy, Clone, Default)]
pub struct Context;

impl crate::context::Context for Context {
    fn set_jump(&mut self) -> bool {
        todo!();
    }

    fn long_jump(&self) -> ! {
        todo!();
    }
}
