#[cfg(feature = "rv32")]
use super::rv32::RV32 as ArchImpl;
#[cfg(feature = "rv64")]
use super::rv64::RV64 as ArchImpl;

pub mod barrier;
pub(super) mod cpu;
pub(super) mod interrupt;
