use core::arch::x86_64::__cpuid;

use x86_64::registers::model_specific::Msr;

use super::{
    msr::{
        rdmsr_safe, MSR_DRAM_ENERGY_STATUS, MSR_PKG_ENERGY_STATUS, MSR_PP0_ENERGY_STATUS,
        MSR_PP1_ENERGY_STATUS, MSR_RAPL_POWER_UNIT,
    },
    X86,
};
use crate::delay;

/// Snapshot of RAPL energy counters read from MSRs.
///
/// Each field is the raw 32-bit counter value from the corresponding MSR.
/// `None` indicates the domain is not supported on this platform.
/// Convert to joules: `raw * 2^(-energy_unit)`.
#[derive(Debug, Clone, Copy)]
pub struct RaplEnergy {
    /// Package energy (MSR 0x611). None if unsupported.
    pub pkg: Option<u32>,
    /// DRAM energy (MSR 0x619). None if unsupported.
    pub dram: Option<u32>,
    /// PP0 (CPU cores) energy (MSR 0x639). None if unsupported.
    pub pp0: Option<u32>,
    /// PP1 (uncore/iGPU) energy (MSR 0x641). None if unsupported.
    pub pp1: Option<u32>,
    /// Energy unit exponent from MSR_RAPL_POWER_UNIT bits [12:8].
    /// 1 LSB = 1 / 2^energy_unit joules.
    pub energy_unit: u32,
}

/// Average power derived from two `RaplEnergy` snapshots, in microwatts.
///
/// `None` in each field means the domain was unsupported in either snapshot.
#[derive(Debug, Clone, Copy)]
pub struct RaplPower {
    /// Package power in microwatts.
    pub pkg_uw: Option<u64>,
    /// DRAM power in microwatts.
    pub dram_uw: Option<u64>,
    /// PP0 (CPU cores) power in microwatts.
    pub pp0_uw: Option<u64>,
    /// PP1 (uncore/iGPU) power in microwatts.
    pub pp1_uw: Option<u64>,
}

impl X86 {
    /// Returns `true` if this CPU advertises Intel RAPL support.
    ///
    /// The definitive check is attempted by `rapl_read_energy`, which returns
    /// `None` when the hardware does not respond to the MSRs.
    pub fn rapl_is_supported() -> bool {
        // CPUID leaf 0: vendor must be "GenuineIntel"
        let vendor = unsafe { __cpuid(0x0) };
        vendor.ebx == 0x756e6547 // "Genu"
            && vendor.ecx == 0x6c65746e // "ntel"
            && vendor.edx == 0x49656e69 // "ineI"
    }

    /// Read a snapshot of RAPL energy counters.
    ///
    /// Returns `None` on non-Intel CPUs or when MSRs are inaccessible.
    /// On AMD, Intel-specific RAPL MSRs may cause an unrecoverable #GP loop
    /// via `rdmsr_safe`, so this function guards with a vendor check first.
    pub fn rapl_read_energy() -> Option<RaplEnergy> {
        // rdmsr_safe relies on GPF being a fault (re-executes the faulting
        // instruction), which causes an infinite #GP loop on AMD where these
        // Intel-specific MSR addresses are not implemented.
        if !Self::rapl_is_supported() {
            return None;
        }

        let power_unit_raw = unsafe { rdmsr_safe(&Msr::new(MSR_RAPL_POWER_UNIT))? };

        // Bits [12:8]: energy status unit exponent
        let energy_unit = ((power_unit_raw >> 8) & 0x1f) as u32;

        let read32 = |addr: u32| -> Option<u32> {
            unsafe { rdmsr_safe(&Msr::new(addr)).map(|v| v as u32) }
        };

        Some(RaplEnergy {
            pkg: read32(MSR_PKG_ENERGY_STATUS),
            dram: read32(MSR_DRAM_ENERGY_STATUS),
            pp0: read32(MSR_PP0_ENERGY_STATUS),
            pp1: read32(MSR_PP1_ENERGY_STATUS),
            energy_unit,
        })
    }

    /// Measure average power by taking two energy snapshots `interval_ms` apart.
    ///
    /// Returns `None` if RAPL is not accessible.
    pub fn rapl_measure_power(interval_ms: u64) -> Option<RaplPower> {
        let e1 = Self::rapl_read_energy()?;
        delay::wait_millisec(interval_ms);
        let e2 = Self::rapl_read_energy()?;
        Some(energy_diff_to_power(&e1, &e2, interval_ms))
    }
}

/// Convert two energy snapshots to average power in microwatts.
///
/// Uses wrapping subtraction to handle the 32-bit counter roll-over.
/// Formula: power_uw = delta_raw * 1_000_000_000 / (2^energy_unit * interval_ms)
fn energy_diff_to_power(e1: &RaplEnergy, e2: &RaplEnergy, interval_ms: u64) -> RaplPower {
    let unit = e1.energy_unit;
    let divisor = (1u64 << unit).saturating_mul(interval_ms);

    let to_uw = |a: Option<u32>, b: Option<u32>| -> Option<u64> {
        let delta = b?.wrapping_sub(a?) as u64;
        delta.checked_mul(1_000_000_000)?.checked_div(divisor)
    };

    RaplPower {
        pkg_uw: to_uw(e1.pkg, e2.pkg),
        dram_uw: to_uw(e1.dram, e2.dram),
        pp0_uw: to_uw(e1.pp0, e2.pp0),
        pp1_uw: to_uw(e1.pp1, e2.pp1),
    }
}
