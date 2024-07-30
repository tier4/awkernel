#[cfg(all(feature = "aarch64", not(feature = "std")))]
mod aarch64;

#[cfg(all(feature = "x86", not(feature = "std")))]
mod x86_64;

#[cfg(all(feature = "rv32", not(feature = "std")))]
mod rv32;

#[cfg(all(feature = "rv64", not(feature = "std")))]
mod rv64;

#[cfg(feature = "std")]
mod std_common;

/// Configuration.
pub mod config;

