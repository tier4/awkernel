use super::rdmsr_safe;
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0x198;
const PERFORMANCE_STATE_OFFSET: u64 = 0; // TODO

#[derive(Debug, Clone, Copy)]
pub struct Ia32PerfStatus(u64);

impl Ia32PerfStatus {
    pub const fn new(msr_value: u64) -> Self {
        Self(msr_value)
    }

    pub const fn raw(&self) -> u64 {
        self.0
    }

    pub const fn performance_state(&self) -> Option<u16> {
        match (self.0 >> PERFORMANCE_STATE_OFFSET) as u16 {
            0 => None,
            ratio => Some(ratio),
        }
    }
}

#[inline]
pub fn try_read() -> Option<Ia32PerfStatus> {
    // Safety: reading MSR_IA32_PM_REQUEST_PKG has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(Ia32PerfStatus::new)
}

/// Writes the IA32_PERF_STATUS MSR without checking for errors.
///     
/// # Safety
///
/// The caller must ensure that IA32_PERF_STATUS MSR is available
#[inline]
pub unsafe fn read_unchecked() -> Ia32PerfStatus {
    Ia32PerfStatus(Msr::new(MSR_NUMBER).read())
}
