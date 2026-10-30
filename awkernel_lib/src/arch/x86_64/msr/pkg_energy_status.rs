//! `MSR_PKG_ENERGY_STATUS`: energy consumed by the whole package.
//!
//! The counter is in the units of [`super::rapl_power_unit`] and wraps around at 32 bits.

use super::rdmsr_safe;
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0x611;

/// Read the raw energy counter.
#[inline]
pub fn try_read() -> Option<u32> {
    // Safety: reading MSR_PKG_ENERGY_STATUS has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(|value| value as u32)
}
