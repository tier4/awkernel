pub use crate::arch::ArchContext;

pub trait Context: Default {
    /// Return `true` when jumped from `long_jump`.
    /// Return `false` when called directly.
    ///
    /// This function must be inline.
    /// So, use ` #[inline(always)]` for implementation.
    fn set_jump(&mut self) -> bool;

    unsafe fn long_jump(&self) -> !;

    unsafe fn set_stack_pointer(&mut self, sp: usize);

    unsafe fn set_entry_point(&mut self, entry: extern "C" fn(usize) -> !, arg: usize);

    unsafe fn set_argument(&mut self, arg: usize);
}
