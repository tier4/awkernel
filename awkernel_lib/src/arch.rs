#[cfg(all(feature = "aarch64", not(feature = "std")))]
pub mod aarch64;

#[cfg(all(feature = "x86", not(feature = "std")))]
pub mod x86_64;

#[cfg(all(feature = "rv32", not(feature = "std")))]
pub mod rv32;

#[cfg(all(feature = "rv64", not(feature = "std")))]
pub mod rv64;

#[cfg(feature = "std")]
pub mod std_common;

#[cfg(all(feature = "aarch64", not(feature = "std")))]
pub(crate) use self::aarch64::AArch64 as ArchImpl;

#[cfg(all(feature = "x86", not(feature = "std")))]
pub(crate) use self::x86_64::X86 as ArchImpl;

#[cfg(all(feature = "rv32", not(feature = "std")))]
pub(crate) use self::rv32::RV32 as ArchImpl;

#[cfg(all(feature = "rv64", not(feature = "std")))]
pub(crate) use self::rv64::RV64 as ArchImpl;

#[cfg(feature = "std")]
pub(crate) use self::std_common::StdCommon as ArchImpl;

#[allow(dead_code)]
#[cfg(not(feature = "std"))]
trait Arch:
    super::delay::Delay
    + super::interrupt::Interrupt
    + super::cpu::CPU
    + super::paging::Mapper
    + super::dvfs::Dvfs
{
}

#[allow(dead_code)]
#[cfg(feature = "std")]
trait Arch: super::delay::Delay + super::interrupt::Interrupt + super::cpu::CPU {}
