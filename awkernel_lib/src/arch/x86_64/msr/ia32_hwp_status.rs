use super::rdmsr_safe;
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0x777;
const GUARANTEED_PERFORMANCE_CHANGE_OFFSET: u64 = 0;
const EXCURSION_MINIMUM_OFFSET: u64 = 2;

#[derive(Debug, Clone, Copy)]
pub struct Ia32HwpStatus(u64);

impl Ia32HwpStatus {
    pub const fn new(msr_value: u64) -> Self {
        Self(msr_value)
    }

    pub const fn guaranteed_performance_change(&self) -> bool {
        self.0 & (1 << GUARANTEED_PERFORMANCE_CHANGE_OFFSET) != 0
    }

    pub const fn excursion_minimum(&self) -> bool {
        self.0 & (1 << EXCURSION_MINIMUM_OFFSET) != 0
    }
}

#[inline]
pub fn try_read() -> Option<Ia32HwpStatus> {
    // Safety: reading MSR_IA32_PM_REQUEST_PKG has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(Ia32HwpStatus::new)
}
