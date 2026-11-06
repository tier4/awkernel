//! Processor vendor identification from CPUID leaf 0.

use super::try_read_leaf;
use core::arch::x86_64::CpuidResult;

const LEAF_NUMBER: u32 = 0x00;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Vendor {
    Intel,
    Amd,
}

pub struct VendorInfo(CpuidResult);

impl VendorInfo {
    pub const fn new(cpuid_result: CpuidResult) -> Self {
        Self(cpuid_result)
    }

    /// Returns the recognized vendor, or `None` for other vendor identifiers.
    pub const fn vendor(&self) -> Option<Vendor> {
        let ebx = self.0.ebx.to_le_bytes();
        let edx = self.0.edx.to_le_bytes();
        let ecx = self.0.ecx.to_le_bytes();
        match (&ebx, &edx, &ecx) {
            (b"Genu", b"ineI", b"ntel") => Some(Vendor::Intel),
            (b"Auth", b"enti", b"cAMD") => Some(Vendor::Amd),
            _ => None,
        }
    }
}

#[inline]
pub fn try_read() -> Option<VendorInfo> {
    try_read_leaf(LEAF_NUMBER).map(VendorInfo::new)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recognizes_vendor_identifiers() {
        for (identifier, expected) in [
            (*b"GenuineIntel", Some(Vendor::Intel)),
            (*b"AuthenticAMD", Some(Vendor::Amd)),
            (*b"UnknownCPU!!", None),
        ] {
            let info = VendorInfo::new(CpuidResult {
                eax: 0,
                ebx: u32::from_le_bytes(identifier[0..4].try_into().unwrap()),
                edx: u32::from_le_bytes(identifier[4..8].try_into().unwrap()),
                ecx: u32::from_le_bytes(identifier[8..12].try_into().unwrap()),
            });
            assert_eq!(info.vendor(), expected);
        }
    }
}
