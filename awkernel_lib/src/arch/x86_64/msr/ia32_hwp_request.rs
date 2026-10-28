use super::{rdmsr_safe, wrmsr_safe};
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0x774;
const MINIMUM_PERFORMANCE_OFFSET: u64 = 0;
const MAXIMUM_PERFORMANCE_OFFSET: u64 = 8;
const DESIRED_PERFORMANCE_OFFSET: u64 = 16;
const ENERGY_PERFORMANCE_OFFSET: u64 = 24;
const ACTIVITY_WINDOW_OFFSET: u64 = 32;
const PACKAGE_CONTROL_OFFSET: u64 = 42;

#[derive(Debug, Clone, Copy)]
pub struct Ia32HwpRequest(u64);

impl Ia32HwpRequest {
    pub const fn new(msr_value: u64) -> Self {
        Self(msr_value)
    }

    pub const fn raw(&self) -> u64 {
        self.0
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

    pub const fn package_control(&self) -> bool {
        self.0 & (1 << PACKAGE_CONTROL_OFFSET) != 0
    }

    pub const fn set_min_perf_ratio(&mut self, ratio: u8) {
        self.0 &= !(0xff << MINIMUM_PERFORMANCE_OFFSET);
        self.0 |= (ratio as u64) << MINIMUM_PERFORMANCE_OFFSET;
    }

    pub const fn set_max_perf_ratio(&mut self, ratio: u8) {
        self.0 &= !(0xff << MAXIMUM_PERFORMANCE_OFFSET);
        self.0 |= (ratio as u64) << MAXIMUM_PERFORMANCE_OFFSET;
    }

    pub const fn set_desired_perf_ratio(&mut self, ratio: u8) {
        self.0 &= !(0xff << DESIRED_PERFORMANCE_OFFSET);
        self.0 |= (ratio as u64) << DESIRED_PERFORMANCE_OFFSET;
    }

    pub const fn set_energy_perf_ratio(&mut self, ratio: u8) {
        self.0 &= !(0xff << ENERGY_PERFORMANCE_OFFSET);
        self.0 |= (ratio as u64) << ENERGY_PERFORMANCE_OFFSET;
    }
}

#[inline]
pub fn try_read() -> Option<Ia32HwpRequest> {
    // Safety: reading MSR_IA32_PM_REQUEST_PKG has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(Ia32HwpRequest::new)
}

#[inline]
pub fn try_write(request: Ia32HwpRequest) -> bool {
    unsafe { wrmsr_safe(&mut Msr::new(MSR_NUMBER), request.raw()) }
}

/// Reads the IA32_HWP_REQUEST MSR without checking for errors.
///
/// # Safety
///
/// The caller must ensure that IA32_HWP_REQUEST MSR is available
#[inline]
pub unsafe fn read_unchecked() -> Ia32HwpRequest {
    Ia32HwpRequest::new(Msr::new(MSR_NUMBER).read())
}

/// Writes the IA32_HWP_REQUEST MSR without checking for errors.
///
/// # Safety
///
/// The caller must ensure that IA32_HWP_REQUEST MSR is available
#[inline]
pub unsafe fn write_unchecked(request: Ia32HwpRequest) {
    Msr::new(MSR_NUMBER).write(request.raw());
}
