use super::try_read_leaf;
use core::arch::x86_64::CpuidResult;

const LEAF_NUMBER: u32 = 0x1A;
const CORE_TYPE_OFFSET: u32 = 24;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CoreType {
    PCore,
    ECore,
}

impl CoreType {
    pub const fn is_pcore(&self) -> bool {
        matches!(self, Self::PCore)
    }

    pub const fn is_ecore(&self) -> bool {
        matches!(self, Self::ECore)
    }
}

pub struct CoreInfo(CpuidResult);

impl CoreInfo {
    pub const fn new(cpuid_result: CpuidResult) -> Self {
        Self(cpuid_result)
    }

    pub const fn core_type(&self) -> Option<CoreType> {
        match (self.0.eax >> CORE_TYPE_OFFSET) as u8 {
            0x40 => Some(CoreType::PCore),
            0x20 => Some(CoreType::ECore),
            _ => None,
        }
    }
}

pub fn try_read() -> Option<CoreInfo> {
    try_read_leaf(LEAF_NUMBER).map(CoreInfo::new)
}
