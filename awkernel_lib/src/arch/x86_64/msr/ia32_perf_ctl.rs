use super::{super::cpuid::freq_info, rdmsr_safe, wrmsr_safe};
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0x199;
const PERFORMANCE_STATE_VOLTAGE_OFFSET: u64 = 0;
const PERFORMANCE_STATE_FREQ_OFFSET: u64 = 8;
const IDA_ENGAGE_OFFSET: u64 = 32;

#[inline]
pub fn ratio_to_hz(ratio: u8) -> u64 {
    freq_info::bus_freq_hz() * ratio as u64
}

#[inline]
pub fn hz_to_ratio(freq: u64) -> u8 {
    freq.div_ceil(freq_info::bus_freq_hz()).min(255) as u8
}

#[derive(Debug, Clone, Copy)]
pub struct Ia32PerfCtl(u64);

impl Ia32PerfCtl {
    pub const fn new(msr_value: u64) -> Self {
        Self(msr_value)
    }

    pub const fn raw(&self) -> u64 {
        self.0
    }

    pub const fn performance_state_voltage(&self) -> Option<u8> {
        match (self.0 >> PERFORMANCE_STATE_VOLTAGE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn performance_state_freq(&self) -> Option<u8> {
        match (self.0 >> PERFORMANCE_STATE_FREQ_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn ida_engage(&self) -> bool {
        self.0 & (1 << IDA_ENGAGE_OFFSET) != 0
    }

    pub const fn set_performance_state_freq(&mut self, ratio: u8) {
        self.0 &= !(0xFF << PERFORMANCE_STATE_FREQ_OFFSET);
        self.0 |= (ratio as u64) << PERFORMANCE_STATE_FREQ_OFFSET;
    }

    pub const fn set_ida_engage(&mut self, engage: bool) {
        if engage {
            self.0 |= 1 << IDA_ENGAGE_OFFSET;
        } else {
            self.0 &= !(1 << IDA_ENGAGE_OFFSET);
        }
    }
}

#[inline]
pub fn try_read() -> Option<Ia32PerfCtl> {
    // Safety: reading MSR_IA32_PM_REQUEST_PKG has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(Ia32PerfCtl::new)
}

#[inline]
pub fn try_write(hwp_status: Ia32PerfCtl) -> bool {
    unsafe { wrmsr_safe(&mut Msr::new(MSR_NUMBER), hwp_status.0) }
}

/// Reads the IA32_PERF_CTL MSR without checking for errors.
///
/// # Safety
///
/// The caller must ensure that IA32_PERF_CTL MSR is available
#[inline]
pub unsafe fn read_unchecked() -> Ia32PerfCtl {
    Ia32PerfCtl(Msr::new(MSR_NUMBER).read())
}

/// Writes the IA32_PERF_CTL MSR without checking for errors.
///
/// # Safety
///
/// The caller must ensure that IA32_PERF_CTL MSR is available
#[inline]
pub unsafe fn write_unchecked(value: Ia32PerfCtl) {
    Msr::new(MSR_NUMBER).write(value.raw());
}
