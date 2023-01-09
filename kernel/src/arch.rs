#[cfg(feature = "aarch64")]
mod aarch64;

#[cfg(feature = "x86")]
mod x86_64;

#[cfg(feature = "linux")]
pub mod linux;

pub mod config;

#[cfg(feature = "aarch64")]
use self::aarch64 as arch_mod;

#[cfg(feature = "x86")]
use self::x86_64 as arch_mod;

#[cfg(feature = "linux")]
use self::linux as arch_mod;

pub type ArchDelay = arch_mod::delay::ArchDelay;

unsafe fn puts(data: &str) {
    arch_mod::puts(data);
}
