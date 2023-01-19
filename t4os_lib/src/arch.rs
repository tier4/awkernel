#[cfg(all(target_arch = "aarch64", not(target_os = "linux")))]
pub mod aarch64;

#[cfg(all(target_arch = "x86_64", not(target_os = "linux")))]
pub mod x86_64;

#[cfg(target_os = "linux")]
pub mod linux;

#[cfg(all(target_arch = "aarch64", not(target_os = "linux")))]
use self::aarch64 as arch_mod;

#[cfg(all(target_arch = "x86_64", not(target_os = "linux")))]
use self::x86_64 as arch_mod;

#[cfg(target_os = "linux")]
use self::linux as arch_mod;

pub(crate) type ArchDelay = arch_mod::delay::ArchDelay;
