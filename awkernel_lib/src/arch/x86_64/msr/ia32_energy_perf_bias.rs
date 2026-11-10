use super::rdmsr_safe;
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0x1b0;
const POWER_POLICY_PREFERENCE_OFFSET: u64 = 0;

#[derive(Debug, Clone, Copy)]
pub struct Ia32EnergyPerfBias(u64);

impl Ia32EnergyPerfBias {
    pub const fn new(msr_value: u64) -> Self {
        Self(msr_value)
    }

    pub const fn power_policy_preference(&self) -> u8 {
        ((self.0 >> POWER_POLICY_PREFERENCE_OFFSET) & 0xf) as u8
    }
}

#[inline]
pub fn try_read() -> Option<Ia32EnergyPerfBias> {
    // Safety: reading MSR_IA32_PM_REQUEST_PKG has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(Ia32EnergyPerfBias::new)
}
