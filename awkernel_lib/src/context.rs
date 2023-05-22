pub use crate::arch::ArchContext;

pub trait Context: Default {
    /// Return `false` when called directly.
    /// Return `true` when jumped from `long_jump`.
    fn set_jump(&mut self) -> bool;

    fn long_jump(&self) -> !;
}
