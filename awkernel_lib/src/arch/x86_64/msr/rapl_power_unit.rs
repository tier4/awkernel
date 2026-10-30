//! `MSR_RAPL_POWER_UNIT`: scale factors of the RAPL power, energy and time counters.

use super::rdmsr_safe;
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0x606;
const POWER_UNITS_OFFSET: u64 = 0;
const POWER_UNITS_MASK: u64 = 0xF;
const ENERGY_STATUS_UNITS_OFFSET: u64 = 8;
const ENERGY_STATUS_UNITS_MASK: u64 = 0x1F;
const TIME_UNITS_OFFSET: u64 = 16;
const TIME_UNITS_MASK: u64 = 0xF;

/// Width of the energy status counters, which wrap around at `2^32` units.
const ENERGY_COUNTER_BITS: u32 = 32;

#[derive(Debug, Clone, Copy)]
pub struct RaplPowerUnit(u64);

impl RaplPowerUnit {
    pub const fn new(msr_value: u64) -> Self {
        Self(msr_value)
    }

    pub const fn raw(&self) -> u64 {
        self.0
    }

    /// The power unit is `1 / 2^power_units()` W.
    pub const fn power_units(&self) -> u8 {
        ((self.0 >> POWER_UNITS_OFFSET) & POWER_UNITS_MASK) as u8
    }

    /// The energy unit is `1 / 2^energy_status_units()` J.
    pub const fn energy_status_units(&self) -> u8 {
        ((self.0 >> ENERGY_STATUS_UNITS_OFFSET) & ENERGY_STATUS_UNITS_MASK) as u8
    }

    /// The time unit is `1 / 2^time_units()` s.
    pub const fn time_units(&self) -> u8 {
        ((self.0 >> TIME_UNITS_OFFSET) & TIME_UNITS_MASK) as u8
    }

    /// Convert a raw energy counter value to microjoules.
    pub const fn energy_to_uj(&self, raw: u32) -> u64 {
        (raw as u64 * 1_000_000) >> self.energy_status_units()
    }

    /// Value in microjoules at which the energy status counters wrap around.
    pub const fn max_energy_range_uj(&self) -> u64 {
        ((1u64 << ENERGY_COUNTER_BITS) * 1_000_000) >> self.energy_status_units()
    }
}

#[inline]
pub fn try_read() -> Option<RaplPowerUnit> {
    // Safety: reading MSR_RAPL_POWER_UNIT has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(RaplPowerUnit::new)
}
