#[cfg(all(feature = "aarch64", not(feature = "linux")))]
pub use super::aarch64::config::*;

#[cfg(all(feature = "x86", not(feature = "linux")))]
pub use super::x86_64::config::*;

#[cfg(all(feature = "rv32"))]
pub use super::rv32::config::*;
