use core::arch::x86_64::{__cpuid, CpuidResult};

pub mod core_type;
pub mod freq_info;
pub mod tpm_info;

/// Whether CPUID supports the basic `leaf`.
///
/// Executing CPUID with an unsupported leaf does not fault, but returns unrelated data.
#[inline]
pub fn supports_basic_leaf(leaf: u32) -> bool {
    __cpuid(0).eax >= leaf
}

#[inline]
pub fn try_read_leaf(leaf: u32) -> Option<CpuidResult> {
    supports_basic_leaf(leaf).then(|| __cpuid(leaf))
}
