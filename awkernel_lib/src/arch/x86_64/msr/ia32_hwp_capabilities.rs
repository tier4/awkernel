use super::{
    super::cpuid::{
        core_type::{self, CoreType},
        freq_info,
    },
    rdmsr_safe,
};
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0x771;
const HIGHEST_PERFORMANCE_OFFSET: u64 = 0;
const GUARANTEED_PERFORMANCE_OFFSET: u64 = 8;
const MOST_EFFICIENT_PERFORMANCE_OFFSET: u64 = 16;
const LOWEST_PERFORMANCE_OFFSET: u64 = 24;

#[inline]
pub fn base_freq_hz() -> u64 {
    match core_type::try_read().and_then(|core_type| core_type.core_type()) {
        Some(CoreType::PCore) => 78_741_000, // TODO review
        _ => freq_info::bus_freq_hz(),
    }
}

/// Hertz per HWP performance unit. HWP units are not 100 MHz ratios on hybrid CPUs:
/// Alder Lake P-cores use 78.741 MHz, as Linux's intel_pstate does.
#[inline]
pub fn ratio_to_hz(ratio: u8) -> u64 {
    base_freq_hz() * ratio as u64
}

pub fn hz_to_ratio(freq: u64) -> u8 {
    freq.div_ceil(base_freq_hz()).min(255) as u8
}

#[derive(Debug, Clone, Copy)]
pub struct Ia32HwpCapabilities(u64);

impl Ia32HwpCapabilities {
    pub const fn new(msr_value: u64) -> Self {
        Self(msr_value)
    }

    pub const fn raw(&self) -> u64 {
        self.0
    }

    pub const fn highest_perf_ratio(&self) -> Option<u8> {
        match (self.0 >> HIGHEST_PERFORMANCE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn guaranteed_perf_ratio(&self) -> Option<u8> {
        match (self.0 >> GUARANTEED_PERFORMANCE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn most_efficient_perf_ratio(&self) -> Option<u8> {
        match (self.0 >> MOST_EFFICIENT_PERFORMANCE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn lowest_perf_ratio(&self) -> Option<u8> {
        match (self.0 >> LOWEST_PERFORMANCE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub fn highest_perf_freq_hz(&self) -> Option<u64> {
        self.highest_perf_ratio().map(ratio_to_hz)
    }

    pub fn guaranteed_perf_freq_hz(&self) -> Option<u64> {
        self.guaranteed_perf_ratio().map(ratio_to_hz)
    }

    pub fn most_efficient_perf_freq_hz(&self) -> Option<u64> {
        self.most_efficient_perf_ratio().map(ratio_to_hz)
    }

    pub fn lowest_perf_freq_hz(&self) -> Option<u64> {
        self.lowest_perf_ratio().map(ratio_to_hz)
    }
}

#[inline]
pub fn try_read() -> Option<Ia32HwpCapabilities> {
    // Safety: reading MSR_IA32_PM_ENABLE has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(Ia32HwpCapabilities::new)
}

/// Reads the IA32_HWP_CAPABILITIES MSR without checking for errors.
///
/// # Safety
///
/// The caller must ensure that IA32_HWP_CAPABILITIES MSR is available
#[inline]
pub unsafe fn read_unchecked() -> Ia32HwpCapabilities {
    Ia32HwpCapabilities::new(Msr::new(MSR_NUMBER).read())
}
