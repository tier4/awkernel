use super::{super::cpuid::freq_info, rdmsr_safe};
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0xCE;
const MAX_NONTURBO_OFFSET: u64 = 8;
const MAX_EFFICIENCY_OFFSET: u32 = 40;
const MIN_OPERATING_OFFSET: u32 = 48;

#[derive(Debug, Clone, Copy)]
pub struct PlatformInfo(u64);

impl PlatformInfo {
    pub const fn new(msr_value: u64) -> Self {
        Self(msr_value)
    }

    pub const fn max_nonturbo_ratio(&self) -> Option<u8> {
        match (self.0 >> MAX_NONTURBO_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn max_efficiency_ratio(&self) -> Option<u8> {
        match (self.0 >> MAX_EFFICIENCY_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn min_operating_ratio(&self) -> Option<u8> {
        match (self.0 >> MIN_OPERATING_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub fn max_nonturbo_freq_mhz(&self) -> Option<u32> {
        self.max_nonturbo_ratio()
            .map(|ratio| ratio as u32 * freq_info::bus_freq_mhz() as u32)
    }

    pub fn max_efficiency_freq_mhz(&self) -> Option<u32> {
        self.max_efficiency_ratio()
            .map(|ratio| ratio as u32 * freq_info::bus_freq_mhz() as u32)
    }

    pub fn min_operating_freq_mhz(&self) -> Option<u32> {
        self.min_operating_ratio()
            .map(|ratio| ratio as u32 * freq_info::bus_freq_mhz() as u32)
    }

    pub fn max_nonturbo_freq_hz(&self) -> Option<u64> {
        self.max_nonturbo_ratio()
            .map(|ratio| ratio as u64 * freq_info::bus_freq_hz())
    }

    pub fn max_efficiency_freq_hz(&self) -> Option<u64> {
        self.max_efficiency_ratio()
            .map(|ratio| ratio as u64 * freq_info::bus_freq_hz())
    }

    pub fn min_operating_freq_hz(&self) -> Option<u64> {
        self.min_operating_ratio()
            .map(|ratio| ratio as u64 * freq_info::bus_freq_hz())
    }
}

#[inline]
pub fn try_read() -> Option<PlatformInfo> {
    // Safety: readinf MSR_PLATFORM_INFO has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(PlatformInfo::new)
}
