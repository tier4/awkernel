#[cfg(all(feature = "aarch64", not(feature = "std")))]
pub mod aarch64;

#[cfg(all(feature = "x86", not(feature = "std")))]
pub mod x86_64;

#[cfg(all(feature = "rv32", not(feature = "std")))]
pub mod rv32;

#[cfg(feature = "std")]
pub mod std_common;

#[cfg(all(feature = "aarch64", not(feature = "std")))]
use self::aarch64 as arch_mod;

#[cfg(all(feature = "x86", not(feature = "std")))]
use self::x86_64 as arch_mod;

#[cfg(all(feature = "rv32", not(feature = "std")))]
use self::rv32 as arch_mod;

#[cfg(feature = "std")]
use self::std_common as arch_mod;

pub(crate) type ArchDelay = arch_mod::delay::ArchDelay;
pub(crate) type ArchInterrupt = arch_mod::interrupt::ArchInterrupt;

#[cfg(not(feature = "std"))]
pub type ArchContext = arch_mod::context::Context;

#[cfg(not(feature = "std"))]
pub(crate) type ArchCPU = arch_mod::cpu::ArchCPU;
