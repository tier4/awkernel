use super::{rdmsr_safe, wrmsr_safe};
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0x770;
const HWP_ENABLE_MASK: u64 = 1 << 0;

#[derive(Debug, Clone, Copy)]
pub struct Ia32PmEnable(u64);

impl Ia32PmEnable {
    pub const fn new(msr_value: u64) -> Self {
        Self(msr_value)
    }

    pub const fn hwp_enabled(&self) -> bool {
        self.0 & HWP_ENABLE_MASK != 0
    }

    pub const fn enable_hwp(&mut self) {
        self.0 |= HWP_ENABLE_MASK;
    }
}

#[inline]
pub fn try_read() -> Option<Ia32PmEnable> {
    // Safety: reading MSR_IA32_PM_ENABLE has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(Ia32PmEnable::new)
}

#[inline]
pub fn try_write(pm_enable: Ia32PmEnable) -> bool {
    unsafe { wrmsr_safe(&mut Msr::new(MSR_NUMBER), pm_enable.0) }
}

#[inline]
pub fn hwp_enabled() -> bool {
    try_read().is_some_and(|pm_enable| pm_enable.hwp_enabled())
}

#[inline]
pub fn enable_hwp() -> bool {
    match try_read() {
        Some(mut pm_enable) => {
            pm_enable.enable_hwp();
            try_write(pm_enable)
        }
        None => false,
    }
}
