//! Processor family and model identification from CPUID leaf 1.

use super::{core_type::CoreType, try_read_leaf, vendor_info::Vendor};
use core::arch::x86_64::CpuidResult;

const LEAF_NUMBER: u32 = 0x01;
const EAX_BASE_MODEL_OFFSET: u32 = 4;
const EAX_BASE_FAMILY_OFFSET: u32 = 8;
const EAX_EXTENDED_MODEL_OFFSET: u32 = 16;
const EAX_EXTENDED_FAMILY_OFFSET: u32 = 20;

/// Intel model groups recognized by this module, not an exhaustive model list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntelModel {
    AlderLake,
    RaptorLake,
    BartlettLake,
    MeteorLake,
    LunarLake,
}

impl IntelModel {
    pub const fn try_from_display_model(display_family: u16, display_model: u8) -> Option<Self> {
        match display_family {
            6 => match display_model {
                0x97 | 0x9a => Some(Self::AlderLake),
                0xb7 | 0xba | 0xbf => Some(Self::RaptorLake),
                0xd7 => Some(Self::BartlettLake),
                0xaa | 0xac => Some(Self::MeteorLake),
                0xbd => Some(Self::LunarLake),
                _ => None,
            },
            _ => None,
        }
    }

    /// Hertz per HWP performance unit using Linux intel_pstate's P-core scaling.
    /// Applies the model factor unless explicitly enumerated as an E-core.
    pub const fn base_freq_hz(&self, core_type: Option<CoreType>) -> Option<u64> {
        match core_type {
            Some(CoreType::PCore) | None => Some(match self {
                Self::AlderLake | Self::RaptorLake | Self::BartlettLake => 78_741_000,
                Self::MeteorLake => 80_000_000,
                Self::LunarLake => 86_957_000,
            }),
            Some(CoreType::ECore) => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Model {
    Intel(IntelModel),
}

impl Model {
    pub const fn try_from_display_model(
        vendor: Vendor,
        display_family: u16,
        display_model: u8,
    ) -> Option<Self> {
        match vendor {
            Vendor::Intel => {
                match IntelModel::try_from_display_model(display_family, display_model) {
                    Some(model) => Some(Self::Intel(model)),
                    None => None,
                }
            }
            _ => None,
        }
    }

    pub const fn base_freq_hz(&self, core_type: Option<CoreType>) -> Option<u64> {
        match self {
            Self::Intel(model) => model.base_freq_hz(core_type),
        }
    }
}

pub struct ProcessorInfo(CpuidResult);

impl ProcessorInfo {
    pub const fn new(cpuid_result: CpuidResult) -> Self {
        Self(cpuid_result)
    }

    const fn base_model(&self) -> u8 {
        ((self.0.eax >> EAX_BASE_MODEL_OFFSET) & 0xf) as u8
    }

    const fn base_family(&self) -> u8 {
        ((self.0.eax >> EAX_BASE_FAMILY_OFFSET) & 0xf) as u8
    }

    const fn extended_model(&self) -> u8 {
        ((self.0.eax >> EAX_EXTENDED_MODEL_OFFSET) & 0xf) as u8
    }

    const fn extended_family(&self) -> u8 {
        ((self.0.eax >> EAX_EXTENDED_FAMILY_OFFSET) & 0xff) as u8
    }

    /// Display family, including the extended family for base family 0xF.
    pub const fn display_family(&self) -> u16 {
        let base_family = self.base_family() as u16;
        match base_family {
            0xf => base_family + self.extended_family() as u16,
            _ => base_family,
        }
    }

    /// Display model, including the extended model for base families 6 and 0xF.
    pub const fn display_model(&self) -> u8 {
        let base_family = self.base_family();
        let base_model = self.base_model();
        match base_family {
            6 | 0xf => base_model | (self.extended_model() << 4),
            _ => base_model,
        }
    }

    /// Returns a recognized vendor-specific model, or `None` for other processors.
    pub const fn model(&self, vendor: Vendor) -> Option<Model> {
        Model::try_from_display_model(vendor, self.display_family(), self.display_model())
    }
}

#[inline]
pub fn try_read() -> Option<ProcessorInfo> {
    try_read_leaf(LEAF_NUMBER).map(ProcessorInfo::new)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hwp_base_frequency_depends_on_model_and_core_type() {
        for (model, expected_hz) in [
            (IntelModel::AlderLake, 78_741_000),
            (IntelModel::RaptorLake, 78_741_000),
            (IntelModel::BartlettLake, 78_741_000),
            (IntelModel::MeteorLake, 80_000_000),
            (IntelModel::LunarLake, 86_957_000),
        ] {
            assert_eq!(model.base_freq_hz(Some(CoreType::PCore)), Some(expected_hz));
            assert_eq!(model.base_freq_hz(None), Some(expected_hz));
            assert_eq!(model.base_freq_hz(Some(CoreType::ECore)), None);
        }
    }

    fn info(signature: u32) -> ProcessorInfo {
        ProcessorInfo::new(CpuidResult {
            eax: signature,
            ebx: 0,
            ecx: 0,
            edx: 0,
        })
    }

    #[test]
    fn decodes_display_family_and_model() {
        for (signature, family, model) in [
            (0x0009_0673, 6, 0x97),
            (0x008a_0f21, 0x17, 0xa2),
            (0x008a_0521, 5, 2),
            (0x0100_0f00, 0x1f, 0),
            (0x0ff0_0f00, 0x10e, 0),
            (0x1ff0_0f00, 0x10e, 0),
        ] {
            let info = info(signature);
            assert_eq!(info.display_family(), family);
            assert_eq!(info.display_model(), model);
        }
    }

    #[test]
    fn recognizes_only_known_intel_family_six_models() {
        for (model, expected) in [
            (0x97, IntelModel::AlderLake),
            (0x9a, IntelModel::AlderLake),
            (0xb7, IntelModel::RaptorLake),
            (0xba, IntelModel::RaptorLake),
            (0xbf, IntelModel::RaptorLake),
            (0xd7, IntelModel::BartlettLake),
            (0xaa, IntelModel::MeteorLake),
            (0xac, IntelModel::MeteorLake),
            (0xbd, IntelModel::LunarLake),
        ] {
            let signature = ((model & 0xf0) << 12) | (6 << 8) | ((model & 0xf) << 4);
            assert_eq!(
                info(signature).model(Vendor::Intel),
                Some(Model::Intel(expected))
            );
            assert_eq!(info(signature).model(Vendor::Amd), None);
            assert_eq!(
                info((signature & !0xf00) | (0xf << 8)).model(Vendor::Intel),
                None
            );
        }
        assert_eq!(info(0x0006_0650).model(Vendor::Intel), None);
    }
}
