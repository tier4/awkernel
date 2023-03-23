#[cfg(all(feature = "aarch64", not(feature = "linux")))]
pub use super::aarch64::cpu::cpu_id;

#[cfg(all(feature = "x86", not(feature = "linux")))]
pub use super::x86_64::cpu::cpu_id;
