use super::{rdmsr_safe, wrmsr_safe};
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0x1A0;
const ENHANCED_SPEEDSTEP_ENABLE_OFFSET: u64 = 16;

#[derive(Debug, Clone, Copy)]
pub struct Ia32MiscEnable(u64);

impl Ia32MiscEnable {
    pub const fn new(msr_value: u64) -> Self {
        Self(msr_value)
    }

    pub const fn raw(&self) -> u64 {
        self.0
    }

    pub const fn enhanced_speedstep_enable(&self) -> bool {
        self.0 & (1 << ENHANCED_SPEEDSTEP_ENABLE_OFFSET) != 0
    }

    pub const fn set_enhanced_speedstep_enable(&mut self, enable: bool) {
        if enable {
            self.0 |= 1 << ENHANCED_SPEEDSTEP_ENABLE_OFFSET;
        } else {
            self.0 &= !(1 << ENHANCED_SPEEDSTEP_ENABLE_OFFSET);
        }
    }
}

#[inline]
pub fn try_read() -> Option<Ia32MiscEnable> {
    // Safety: reading MSR_IA32_PM_REQUEST_PKG has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(Ia32MiscEnable::new)
}

#[inline]
pub fn try_write(hwp_status: Ia32MiscEnable) -> bool {
    unsafe { wrmsr_safe(&mut Msr::new(MSR_NUMBER), hwp_status.0) }
}

/// Reads the IA32_MISC_ENABLE MSR without checking for errors.
///
/// # Safety
///
/// The caller must ensure that IA32_MISC_ENABLE MSR is available
#[inline]
pub unsafe fn read_unchecked() -> Ia32MiscEnable {
    Ia32MiscEnable(Msr::new(MSR_NUMBER).read())
}

/// Writes the IA32_MISC_ENABLE MSR without checking for errors.
///
/// # Safety
///
/// The caller must ensure that IA32_MISC_ENABLE MSR is available
#[inline]
pub unsafe fn write_unchecked(value: Ia32MiscEnable) {
    Msr::new(MSR_NUMBER).write(value.raw());
}
