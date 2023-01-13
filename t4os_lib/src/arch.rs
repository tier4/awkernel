#[cfg(feature = "aarch64")]
pub mod aarch64;

#[cfg(feature = "x86")]
pub mod x86_64;

#[cfg(feature = "linux")]
pub mod linux;

#[cfg(feature = "aarch64")]
use self::aarch64 as arch_mod;

#[cfg(feature = "x86")]
use self::x86_64 as arch_mod;

#[cfg(feature = "linux")]
use self::linux as arch_mod;

pub(crate) type ArchDelay = arch_mod::delay::ArchDelay;
