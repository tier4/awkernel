#[cfg(any(
    all(
        target_arch = "aarch64",
        not(target_os = "linux"),
        not(target_os = "macos")
    ),
    feature = "aarch64"
))]
pub mod aarch64;

#[cfg(all(feature = "x86", not(feature = "std")))]
pub mod x86_64;

#[cfg(all(feature = "rv32", not(feature = "std")))]
pub mod rv32;

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub mod std_common;

#[cfg(any(
    all(
        target_arch = "aarch64",
        not(target_os = "linux"),
        not(target_os = "macos")
    ),
    feature = "aarch64"
))]
use self::aarch64 as arch_mod;

#[cfg(all(feature = "x86", not(feature = "std")))]
use self::x86_64 as arch_mod;

#[cfg(all(feature = "rv32", not(feature = "std")))]
use self::rv32 as arch_mod;

#[cfg(any(target_os = "macos", target_os = "linux"))]
use self::std_common as arch_mod;

pub(crate) type ArchDelay = arch_mod::delay::ArchDelay;

#[cfg(not(feature = "std"))]
pub(crate) type ArchCPU = arch_mod::cpu::ArchCPU;
