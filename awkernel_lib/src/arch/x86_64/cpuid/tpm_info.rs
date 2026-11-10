//! Thermal and Power Management (TPM) information from CPUID.

use super::try_read_leaf;
use core::arch::x86_64::CpuidResult;

const LEAF_NUMBER: u32 = 0x06;
const EAX_HWP_OFFSET: u32 = 7;
const ECX_HW_COORD_FEEDBACK_OFFSET: u32 = 0;

pub struct ThermalPowerMgmtInfo(CpuidResult);

impl ThermalPowerMgmtInfo {
    pub const fn new(cpuid_result: CpuidResult) -> Self {
        Self(cpuid_result)
    }

    pub const fn hwp(&self) -> bool {
        (self.0.eax & (1 << EAX_HWP_OFFSET)) != 0
    }

    pub const fn hw_coord_feedback(&self) -> bool {
        (self.0.ecx & (1 << ECX_HW_COORD_FEEDBACK_OFFSET)) != 0
    }
}

#[inline]
pub fn try_read() -> Option<ThermalPowerMgmtInfo> {
    try_read_leaf(LEAF_NUMBER).map(ThermalPowerMgmtInfo::new)
}

#[inline]
pub fn hwp_supported() -> bool {
    try_read().is_some_and(|info| info.hwp())
}

#[inline]
pub fn hw_coord_feedback_supported() -> bool {
    try_read().is_some_and(|info| info.hw_coord_feedback())
}
