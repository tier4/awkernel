#[cfg(all(target_arch = "aarch64", not(feature = "linux")))]
mod aarch64;

#[cfg(all(target_arch = "x86_64", not(feature = "linux")))]
mod x86_64;

#[cfg(feature = "linux")]
mod linux;

/// Configuration.
pub mod config;
