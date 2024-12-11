#[cfg(feature = "x86")]
mod x86_64;

#[cfg(feature = "x86")]
pub use crate::interrupt_guard::x86_64::*;

#[cfg(feature = "aarch64")]
mod aarch64;

#[cfg(feature = "aarch64")]
pub use crate::interrupt_guard::aarch64::*;

#[cfg(feature = "std")]
mod std_common;

#[cfg(feature = "std")]
pub use crate::interrupt_guard::std_common::*;

#[cfg(feature = "rv64")]
mod rv64;

#[cfg(feature = "rv64")]
pub use crate::interrupt_guard::rv64::*;

#[cfg(feature = "rv32")]
mod rv32;

#[cfg(feature = "rv32")]
pub use crate::interrupt_guard::rv32::*;

/// Disable interrupts and automatically restored the configuration.
///
/// ```
/// {
///     use awkernel_lib::interrupt::InterruptGuard;
///
///     let _int_guard = InterruptGuard::new();
///     // interrupts are disabled.
/// }
/// // The configuration will be restored here.
/// ```
pub struct InterruptGuard {
    flag: usize,
}

impl Default for InterruptGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl InterruptGuard {
    pub fn new() -> Self {
        let flag = get_flag();
        disable();

        Self { flag }
    }
}

impl Drop for InterruptGuard {
    fn drop(&mut self) {
        set_flag(self.flag);
    }
}
