//! Structured extended feature flags from CPUID leaf 7, subleaf 0.

use super::try_read_leaf;
use core::arch::x86_64::CpuidResult;

const LEAF_NUMBER: u32 = 0x07;
const EDX_HYBRID_OFFSET: u32 = 15;

pub struct StructuredFeatures(CpuidResult);

impl StructuredFeatures {
    pub const fn new(cpuid_result: CpuidResult) -> Self {
        Self(cpuid_result)
    }

    pub const fn hybrid(&self) -> bool {
        self.0.edx & (1 << EDX_HYBRID_OFFSET) != 0
    }
}

#[inline]
pub fn try_read() -> Option<StructuredFeatures> {
    try_read_leaf(LEAF_NUMBER).map(StructuredFeatures::new)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_hybrid_flag() {
        for (edx, expected) in [(0, false), (1 << 15, true), (1 << 14, false)] {
            assert_eq!(
                StructuredFeatures::new(CpuidResult {
                    eax: 0,
                    ebx: 0,
                    ecx: 0,
                    edx,
                })
                .hybrid(),
                expected
            );
        }
    }
}
