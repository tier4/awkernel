#[cfg(all(feature = "aarch64", not(feature = "linux")))]
mod aarch64;

#[cfg(all(feature = "x86", not(feature = "linux")))]
mod x86_64;

#[cfg(feature = "linux")]
mod linux;

/// Configuration.
pub mod config;

/// CPUID
pub mod cpu;
