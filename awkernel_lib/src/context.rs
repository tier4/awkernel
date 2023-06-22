// pub use crate::arch::ArchContext;

#[cfg(target_arch = "aarch64")]
mod aarch64;

#[cfg(target_arch = "aarch64")]
pub use aarch64::Context as ArchContext;

#[cfg(target_arch = "x86_64")]
mod x86_64;

#[cfg(target_arch = "x86_64")]
pub use self::x86_64::Context as ArchContext;

#[cfg(target_arch = "riscv32")]
mod rv32;

#[cfg(target_arch = "riscv32")]
pub use rv32::Context as ArchContext;

extern "C" {
    /// Switch context from `current` to `next`.
    pub fn context_switch(current: *mut ArchContext, next: *const ArchContext);
}

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
