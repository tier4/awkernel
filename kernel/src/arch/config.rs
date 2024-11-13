#[cfg(all(feature = "aarch64", not(feature = "linux")))]
pub use super::aarch64::config::*;

#[cfg(all(feature = "x86", not(feature = "linux")))]
pub use super::x86_64::config::*;

#[cfg(all(feature = "rv32", not(feature = "linux")))]
pub use super::rv32::config::*;

#[cfg(all(feature = "rv64", not(feature = "linux")))]
pub use super::rv64::config::*;

/// Initialize the architecture specific configuration.
///
/// # Safety
///
/// This function must be called before at the beginning of the kernel.
pub unsafe fn init() {
    awkernel_lib::config::set_stack_size(STACK_SIZE);
    awkernel_lib::config::set_stack_start(STACK_START);
}
