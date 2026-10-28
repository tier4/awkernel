use crate::{
    delay::wait_microsec,
    dvfs::{Dvfs, Error, Result},
};

use super::{
    cpuid::{freq_info, tpm_info},
    hwp,
    msr::{ia32_misc_enable, ia32_perf_aperf, ia32_perf_ctl, ia32_perf_mperf, platform_info},
    X86,
};

/// Measure this CPU's average frequency over `interval_us`.
///
/// This function is blocking: it remains on CPU while the sample is collected.
pub fn measure_freq_hz(interval_us: u64) -> Result<u64> {
    if interval_us == 0 {
        return Err(Error::InvalidArgument);
    }
    if !tpm_info::hw_coord_feedback_supported() {
        return Err(Error::NotSupported);
    }
    let base_freq_hz = freq_info::base_freq_hz().ok_or(Error::NotSupported)?;

    // Safety: HW_COORD_FEEDBACK is supported
    let start_mperf = unsafe { ia32_perf_mperf::read_unchecked() };
    let start_aperf = unsafe { ia32_perf_aperf::read_unchecked() };

    wait_microsec(interval_us);

    // Safety: HW_COORD_FEEDBACK is supported
    let end_mperf = unsafe { ia32_perf_mperf::read_unchecked() };
    let end_aperf = unsafe { ia32_perf_aperf::read_unchecked() };

    let mperf_delta = end_mperf.wrapping_sub(start_mperf);
    let aperf_delta = end_aperf.wrapping_sub(start_aperf);
    if mperf_delta == 0 {
        return Err(Error::InternalError);
    }

    let freq_hz = (aperf_delta as u128 * base_freq_hz as u128) / mperf_delta as u128;
    Ok(freq_hz as u64)
}

impl Dvfs for X86 {
    unsafe fn cpu_init() -> Result<()> {
        if !hwp::enable() {
            log::warn!("[DVFS] Failed to enable HWP.");
        }
        let mut misc_enable = ia32_misc_enable::try_read().ok_or(Error::NotSupported)?;
        misc_enable.set_enhanced_speedstep_enable(true);
        // Safety: MSR IA32_MISC_ENABLE exists
        unsafe { ia32_misc_enable::write_unchecked(misc_enable) };
        X86::set_min_cpu_freq()
    }

    /// Fix the frequency of the current CPU.
    fn set_cpu_freq(freq: u64) -> Result<()> {
        // First we check the frequency is within the CPU's range
        let min = Self::get_min_cpu_freq()?;
        let max = Self::get_max_cpu_freq()?;
        if freq < min || freq > max {
            return Err(Error::FrequencyOutOfRange {
                requested: freq,
                min,
                max,
            });
        }
        // Round the frequency to a bus ratio, so the CPU is never below the request
        let freq = ceil_to_bus_ratio(freq).min(max);

        // If HWP is enabled, we use IA32_HWP_REQUEST to set the frequency
        if hwp::is_enabled() {
            return hwp::set_frequency_hz(freq).map_err(|error| error.into());
        }
        // When HWP is not enabled, we try to use IA32_PERF_CTL
        if let Some(mut perf_ctl) = ia32_perf_ctl::try_read() {
            let ratio = ia32_perf_ctl::hz_to_ratio(freq);
            perf_ctl.set_ida_engage(true);
            perf_ctl.set_performance_state_freq(ratio);
            // Safety: IA32_PERF_CTL exists if Enhanced SpeedStep is supported.
            unsafe { ia32_perf_ctl::write_unchecked(perf_ctl) };
            return Ok(());
        }
        Err(Error::NotSupported)
    }

    /// Get the maximum (non-turbo) frequency of the current CPU.
    fn get_max_cpu_freq() -> Result<u64> {
        // If HWP is enabled, we use IA32_HWP_CAPABILITIES to get the guaranteed performance
        if hwp::is_enabled() {
            return hwp::guaranteed_freq_hz()
                .map(floor_to_bus_ratio)
                .map_err(|e| e.into());
        }
        // If HWP is not enabled, we try with the CPUID.16H
        if let Some(freq_hz) = freq_info::base_freq_hz() {
            return Ok(freq_hz);
        }
        // If CPUID.16H not supported, we try with the MSR_PLATFORM_INFO
        platform_info::try_read()
            .and_then(|info| info.max_nonturbo_freq_hz())
            .ok_or(Error::NotSupported)
    }

    /// Get the minimum frequency of the current CPU.
    fn get_min_cpu_freq() -> Result<u64> {
        // We only rely on the platform info MSR to get the minimum frequency.
        platform_info::try_read()
            .and_then(|info| {
                // First, try to get the minimum operating frequency.
                info.min_operating_freq_hz()
                    // If not available, fall back to the maximum efficiency frequency.
                    .or_else(|| info.max_efficiency_freq_hz())
            })
            .map(ceil_to_bus_ratio)
            .ok_or(Error::NotSupported)
    }

    /// Get the current frequency of the current CPU.
    fn get_curr_cpu_freq() -> Result<u64> {
        measure_freq_hz(100_000)
    }
}

/// Round `freq` up to a multiple of the bus clock, so the CPU is never below the request.
#[inline]
fn ceil_to_bus_ratio(freq: u64) -> u64 {
    let bus_hz = freq_info::bus_freq_hz();
    freq.div_ceil(bus_hz) * bus_hz
}

/// Round `freq` down to a multiple of the bus clock.
#[inline]
fn floor_to_bus_ratio(freq: u64) -> u64 {
    let bus_hz = freq_info::bus_freq_hz();
    freq / bus_hz * bus_hz
}
