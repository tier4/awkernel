#[cfg(all(feature = "aarch64", not(feature = "linux")))]
mod aarch64;

#[cfg(all(feature = "x86", not(feature = "linux")))]
mod x86_64;

#[cfg(all(feature = "rv32", not(feature = "linux")))]
mod rv32;

#[cfg(any(feature = "linux", feature = "macos"))]
mod std_common;

/// Configuration.
pub mod config;
