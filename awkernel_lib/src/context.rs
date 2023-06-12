pub use crate::arch::ArchContext;

extern "C" {
    /// Switch context from `current` to `next`.
    pub fn context_switch(current: *mut ArchContext, next: *const ArchContext);
}

pub trait Context: Default {
    unsafe fn set_stack_pointer(&mut self, sp: usize);

    unsafe fn set_entry_point(&mut self, entry: extern "C" fn(usize) -> !, arg: usize);

    unsafe fn set_argument(&mut self, arg: usize);
}
