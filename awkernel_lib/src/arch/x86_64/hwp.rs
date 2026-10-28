//! Pin the calling CPU's frequency with Intel HWP (Speed Shift).
//!
//! The pinned level is the core's own *Guaranteed Performance* from
//! `IA32_HWP_CAPABILITIES`: the highest level the core can sustain within the
//! package's power/thermal budget, i.e. its base frequency with turbo excluded.
//! Each core reports its own value, so on hybrid processors P-cores and E-cores
//! are each pinned to their own base clock.

use super::{
    cpuid::tpm_info,
    msr::{ia32_hwp_capabilities, ia32_hwp_request, ia32_pm_enable},
};
use crate::dvfs::Error as DvfsError;

/// `IA32_HWP_CAPABILITIES` of one logical CPU, in HWP performance units.
#[derive(Debug, Clone, Copy)]
pub struct HwpLevels {
    pub highest: u8,
    pub guaranteed: u8,
    pub lowest: u8,
}

pub fn is_supported() -> bool {
    tpm_info::try_read().is_some_and(|tpm| tpm.hwp())
}

pub fn is_enabled() -> bool {
    is_supported() && ia32_pm_enable::hwp_enabled()
}

pub fn enable() -> bool {
    is_supported() && ia32_pm_enable::enable_hwp()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HwpError {
    /// CPUID.06H:EAX[7] is clear (e.g. under QEMU).
    NotSupported,
    InvalidArgument,
    MsrFault,
}

impl core::fmt::Display for HwpError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            HwpError::NotSupported => write!(f, "HWP not supported"),
            HwpError::InvalidArgument => write!(f, "Invalid argument"),
            HwpError::MsrFault => write!(f, "MSR fault"),
        }
    }
}

impl core::error::Error for HwpError {}

impl From<HwpError> for DvfsError {
    fn from(err: HwpError) -> Self {
        match err {
            HwpError::NotSupported => DvfsError::NotSupported,
            HwpError::InvalidArgument => DvfsError::InvalidArgument,
            HwpError::MsrFault => DvfsError::InternalError,
        }
    }
}

fn levels() -> Result<HwpLevels, HwpError> {
    let caps = ia32_hwp_capabilities::try_read().ok_or(HwpError::MsrFault)?;
    Ok(HwpLevels {
        highest: caps.highest_perf_ratio().ok_or(HwpError::MsrFault)?,
        guaranteed: caps.guaranteed_perf_ratio().ok_or(HwpError::MsrFault)?,
        lowest: caps.lowest_perf_ratio().ok_or(HwpError::MsrFault)?,
    })
}

pub fn highest_freq_hz() -> Result<u64, HwpError> {
    let caps = ia32_hwp_capabilities::try_read().ok_or(HwpError::MsrFault)?;
    caps.highest_perf_freq_hz().ok_or(HwpError::MsrFault)
}

/// Return the guaranteed (non-turbo) frequency for the calling CPU.
pub fn guaranteed_freq_hz() -> Result<u64, HwpError> {
    let caps = ia32_hwp_capabilities::try_read().ok_or(HwpError::MsrFault)?;
    caps.guaranteed_perf_freq_hz().ok_or(HwpError::MsrFault)
}

pub fn lowest_freq_hz() -> Result<u64, HwpError> {
    let caps = ia32_hwp_capabilities::try_read().ok_or(HwpError::MsrFault)?;
    caps.lowest_perf_freq_hz().ok_or(HwpError::MsrFault)
}

/// Convert an absolute frequency to HWP units and request that level.
pub fn set_frequency_hz(freq_hz: u64) -> Result<(), HwpError> {
    if !is_enabled() {
        return Err(HwpError::NotSupported);
    }
    set_perf_ratio(ia32_hwp_capabilities::hz_to_ratio(freq_hz))
}

/// Set the calling CPU to one HWP performance level.
pub fn set_perf_ratio(ratio: u8) -> Result<(), HwpError> {
    set_perf_range(ratio, ratio)
}

/// Set the minimum and maximum HWP performance levels for the calling CPU.
pub fn set_perf_range(minimum: u8, maximum: u8) -> Result<(), HwpError> {
    if !is_enabled() {
        return Err(HwpError::NotSupported);
    }
    if minimum > maximum {
        return Err(HwpError::InvalidArgument);
    }

    let mut request = ia32_hwp_request::Ia32HwpRequest::new(0);
    request.set_min_perf_ratio(minimum);
    request.set_max_perf_ratio(maximum);
    // Safety: HWP is enabled, so writing to IA32_HWP_REQUEST is safe.
    unsafe { ia32_hwp_request::write_unchecked(request) };
    Ok(())
}

/// Enable HWP on the calling CPU and request min = max = guaranteed performance.
///
/// Enabling HWP cannot be undone until reset, which is fine for a kernel that
/// owns the machine for the whole boot.
pub fn pin_to_guaranteed() -> Result<HwpLevels, HwpError> {
    if !is_supported() {
        return Err(HwpError::NotSupported);
    }

    let _int_guard = crate::interrupt::InterruptGuard::new();

    // Safety: HWP support was verified, and enabling it is the requested operation.
    if !enable() {
        return Err(HwpError::MsrFault);
    }

    let levels = levels()?;
    set_perf_ratio(levels.guaranteed)?;
    Ok(levels)
}
