#[cfg(all(target_arch = "aarch64", not(feature = "linux")))]
pub use super::aarch64::config::*;

#[cfg(all(target_arch = "x86_64", not(feature = "linux")))]
pub use super::x86_64::config::*;

#[cfg(feature = "linux")]
pub use super::linux::config::*;
