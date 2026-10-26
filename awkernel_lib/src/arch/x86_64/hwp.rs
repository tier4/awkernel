//! Pin the calling CPU's frequency with Intel HWP (Speed Shift).
//!
//! The pinned level is the core's own *Guaranteed Performance* from
//! `IA32_HWP_CAPABILITIES`: the highest level the core can sustain within the
//! package's power/thermal budget, i.e. its base frequency with turbo excluded.
//! Each core reports its own value, so on hybrid processors P-cores and E-cores
//! are each pinned to their own base clock.

use core::arch::x86_64::__cpuid;

use x86_64::registers::model_specific::Msr;

use super::msr::{rdmsr_safe, wrmsr_safe};

const MSR_IA32_PM_ENABLE: u32 = 0x770;
const MSR_IA32_HWP_CAPABILITIES: u32 = 0x771;
const MSR_IA32_HWP_REQUEST: u32 = 0x774;
const MSR_IA32_APERF: u32 = 0xE8;

/// `IA32_HWP_CAPABILITIES` of one logical CPU, in HWP performance units.
#[derive(Debug, Clone, Copy)]
pub struct HwpLevels {
    pub highest: u8,
    pub guaranteed: u8,
    pub lowest: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HwpError {
    /// CPUID.06H:EAX[7] is clear (e.g. under QEMU).
    NotSupported,
    MsrFault,
}

/// Enable HWP on the calling CPU and request min = max = guaranteed performance.
///
/// Enabling HWP cannot be undone until reset, which is fine for a kernel that
/// owns the machine for the whole boot.
pub fn pin_to_guaranteed() -> Result<HwpLevels, HwpError> {
    if __cpuid(6).eax & (1 << 7) == 0 {
        return Err(HwpError::NotSupported);
    }

    let _int_guard = crate::interrupt::InterruptGuard::new();

    let mut pm_enable = Msr::new(MSR_IA32_PM_ENABLE);
    if !unsafe { wrmsr_safe(&mut pm_enable, 1) } {
        return Err(HwpError::MsrFault);
    }

    let caps =
        unsafe { rdmsr_safe(&Msr::new(MSR_IA32_HWP_CAPABILITIES)) }.ok_or(HwpError::MsrFault)?;
    let [highest, guaranteed, _efficient, lowest, ..] = caps.to_le_bytes();

    // Minimum[7:0] = Maximum[15:8] = guaranteed; Desired[23:16] = 0 (autonomous
    // within [min, max], which is a single point); EPP[31:24] = 0; activity
    // window and package control left 0.
    let g = u64::from(guaranteed);
    let request = g | (g << 8);
    let mut hwp_request = Msr::new(MSR_IA32_HWP_REQUEST);
    if !unsafe { wrmsr_safe(&mut hwp_request, request) } {
        return Err(HwpError::MsrFault);
    }

    Ok(HwpLevels {
        highest,
        guaranteed,
        lowest,
    })
}

/// Measure the calling CPU's actual clock over `window_us` of busy spinning.
///
/// APERF counts actual core cycles while the core is in C0, which a spin keeps
/// it in, so cycles / elapsed microseconds is the running frequency in MHz.
pub fn measure_freq_mhz(window_us: u64) -> Option<u64> {
    let _int_guard = crate::interrupt::InterruptGuard::new();
    let aperf = Msr::new(MSR_IA32_APERF);

    let start_us = crate::delay::uptime();
    let start_cycles = unsafe { rdmsr_safe(&aperf) }?;
    crate::delay::wait_microsec(window_us);
    let end_cycles = unsafe { rdmsr_safe(&aperf) }?;
    let elapsed_us = crate::delay::uptime().saturating_sub(start_us);

    Some(end_cycles.wrapping_sub(start_cycles) / elapsed_us.max(1))
}
