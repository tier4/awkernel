pub use crate::arch::ArchContext;

pub trait Context: Default {
    /// Return `true` when jumped from `long_jump`.
    /// Return `false` when called directly.
    fn set_jump(&mut self) -> bool;

    unsafe fn long_jump(&self) -> !;

    unsafe fn set_stack_pointer(&mut self, sp: usize);

    unsafe fn set_entry_point(&mut self, entry: extern "C" fn(usize) -> !, arg: usize);
}
