use super::{
    super::cpuid::{core_type, freq_info, processor_info, structured_features, vendor_info},
    rdmsr_safe,
};
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0x771;
const HIGHEST_PERFORMANCE_OFFSET: u64 = 0;
const GUARANTEED_PERFORMANCE_OFFSET: u64 = 8;
const MOST_EFFICIENT_PERFORMANCE_OFFSET: u64 = 16;
const LOWEST_PERFORMANCE_OFFSET: u64 = 24;

/// Hertz per HWP performance unit, or `None` for unknown hybrid scaling.
#[inline]
pub fn base_freq_hz() -> Option<u64> {
    let model = vendor_info::try_read()
        .and_then(|info| info.vendor())
        .and_then(|vendor| processor_info::try_read()?.model(vendor));
    let core_type = core_type::try_read().and_then(|info| info.core_type());
    let hybrid = structured_features::try_read().is_some_and(|info| info.hybrid());
    select_base_freq_hz(model, core_type, hybrid, freq_info::bus_freq_hz())
}

fn select_base_freq_hz(
    model: Option<processor_info::Model>,
    core_type: Option<core_type::CoreType>,
    hybrid: bool,
    bus_freq_hz: u64,
) -> Option<u64> {
    match model {
        Some(model) => match model.base_freq_hz(core_type) {
            Some(freq_hz) => Some(freq_hz),
            None => Some(bus_freq_hz),
        },
        None => {
            if hybrid || core_type.is_some() {
                None // Unknown hybrid models require firmware-derived scaling
            } else {
                Some(bus_freq_hz)
            }
        }
    }
}

/// Converts HWP performance units to hertz using known model-specific P-core
/// scaling factors or a supported bus-frequency fallback.
/// Returns `None` if the scaling factor of a hybrid model is unknown.
#[inline]
pub fn ratio_to_hz(ratio: u8) -> Option<u64> {
    base_freq_hz().map(|base| base * ratio as u64)
}

/// Returns `None` if the scaling factor of a hybrid model is unknown.
pub fn hz_to_ratio(freq: u64) -> Option<u8> {
    base_freq_hz().map(|base| freq.div_ceil(base).min(255) as u8)
}

#[derive(Debug, Clone, Copy)]
pub struct Ia32HwpCapabilities(u64);

impl Ia32HwpCapabilities {
    pub const fn new(msr_value: u64) -> Self {
        Self(msr_value)
    }

    pub const fn raw(&self) -> u64 {
        self.0
    }

    pub const fn highest_perf_ratio(&self) -> Option<u8> {
        match (self.0 >> HIGHEST_PERFORMANCE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn guaranteed_perf_ratio(&self) -> Option<u8> {
        match (self.0 >> GUARANTEED_PERFORMANCE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn most_efficient_perf_ratio(&self) -> Option<u8> {
        match (self.0 >> MOST_EFFICIENT_PERFORMANCE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub const fn lowest_perf_ratio(&self) -> Option<u8> {
        match (self.0 >> LOWEST_PERFORMANCE_OFFSET) as u8 {
            0 => None,
            ratio => Some(ratio),
        }
    }

    pub fn highest_perf_freq_hz(&self) -> Option<u64> {
        self.highest_perf_ratio().and_then(ratio_to_hz)
    }

    pub fn guaranteed_perf_freq_hz(&self) -> Option<u64> {
        self.guaranteed_perf_ratio().and_then(ratio_to_hz)
    }

    pub fn most_efficient_perf_freq_hz(&self) -> Option<u64> {
        self.most_efficient_perf_ratio().and_then(ratio_to_hz)
    }

    pub fn lowest_perf_freq_hz(&self) -> Option<u64> {
        self.lowest_perf_ratio().and_then(ratio_to_hz)
    }
}

#[inline]
pub fn try_read() -> Option<Ia32HwpCapabilities> {
    // Safety: reading MSR_IA32_PM_ENABLE has no side effects
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }.map(Ia32HwpCapabilities::new)
}

/// Reads the IA32_HWP_CAPABILITIES MSR without checking for errors.
///
/// # Safety
///
/// The caller must ensure that IA32_HWP_CAPABILITIES MSR is available
#[inline]
pub unsafe fn read_unchecked() -> Ia32HwpCapabilities {
    Ia32HwpCapabilities::new(Msr::new(MSR_NUMBER).read())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arch::x86_64::cpuid::processor_info::IntelModel;

    #[test]
    fn selects_known_model_scaling_without_core_type() {
        for (model, expected) in [
            (IntelModel::AlderLake, 78_741_000),
            (IntelModel::RaptorLake, 78_741_000),
            (IntelModel::BartlettLake, 78_741_000),
            (IntelModel::MeteorLake, 80_000_000),
            (IntelModel::LunarLake, 86_957_000),
        ] {
            for hybrid in [false, true] {
                for core_type in [None, Some(CoreType::PCore)] {
                    assert_eq!(
                        select_base_freq_hz(
                            Some(Model::Intel(model)),
                            core_type,
                            hybrid,
                            100_000_000
                        ),
                        Some(expected)
                    );
                }
                assert_eq!(
                    select_base_freq_hz(
                        Some(Model::Intel(model)),
                        Some(CoreType::ECore),
                        hybrid,
                        100_000_000
                    ),
                    Some(100_000_000)
                );
            }
        }
    }

    #[test]
    fn rejects_unknown_hybrid_scaling() {
        for core_type in [None, Some(CoreType::PCore), Some(CoreType::ECore)] {
            assert_eq!(
                select_base_freq_hz(None, core_type, true, 100_000_000),
                None
            );
        }
        for core_type in [CoreType::PCore, CoreType::ECore] {
            assert_eq!(
                select_base_freq_hz(None, Some(core_type), false, 100_000_000),
                None
            );
        }
        assert_eq!(
            select_base_freq_hz(None, None, false, 100_000_000),
            Some(100_000_000)
        );
    }
}
