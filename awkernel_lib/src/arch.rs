#[cfg(any(
    all(target_arch = "aarch64", not(target_os = "linux")),
    feature = "aarch64"
))]
pub mod aarch64;

#[cfg(all(feature = "x86", not(feature = "std")))]
pub mod x86_64;

#[cfg(feature = "std")]
pub mod linux;

#[cfg(any(
    all(target_arch = "aarch64", not(target_os = "linux")),
    feature = "aarch64"
))]
use self::aarch64 as arch_mod;

#[cfg(all(feature = "x86", not(feature = "std")))]
use self::x86_64 as arch_mod;

#[cfg(feature = "std")]
use self::linux as arch_mod;

pub(crate) type ArchDelay = arch_mod::delay::ArchDelay;

#[cfg(not(target_os = "linux"))]
pub(crate) type ArchCPU = arch_mod::cpu::ArchCPU;
