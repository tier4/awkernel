use super::rdmsr_safe;
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0x772;
const MINIMUM_PERFORMANCE_OFFSET: u64 = 0;
const MAXIMUM_PERFORMANCE_OFFSET: u64 = 8;
const DESIRED_PERFORMANCE_OFFSET: u64 = 16;
const ENERGY_PERFORMANCE_OFFSET: u64 = 24;
const ACTIVITY_WINDOW_OFFSET: u64 = 32;

#[derive(Debug, Clone, Copy)]
pub struct Ia32HwpRequestPkg(u64);

impl Ia32HwpRequestPkg {
    pub const fn new(msr_value: u64) -> Self {
        Self(msr_value)
    }

    pub const fn min_perf_ratio(&self) -> Option<u8> {
        match (self.0 >> MINIMUM_PERFORMANCE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn max_perf_ratio(&self) -> Option<u8> {
        match (self.0 >> MAXIMUM_PERFORMANCE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn desired_perf_ratio(&self) -> Option<u8> {
        match (self.0 >> DESIRED_PERFORMANCE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn energy_perf_ratio(&self) -> Option<u8> {
        match (self.0 >> ENERGY_PERFORMANCE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn activity_window(&self) -> Option<u16> {
        match (self.0 >> ACTIVITY_WINDOW_OFFSET) & 0x3ff {
            0 => None,
            window => Some(window as u16),
        }
    }
}

#[inline]
pub fn try_read() -> Option<Ia32HwpRequestPkg> {
    // Safety: reading MSR_IA32_PM_REQUEST_PKG has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(Ia32HwpRequestPkg::new)
}
