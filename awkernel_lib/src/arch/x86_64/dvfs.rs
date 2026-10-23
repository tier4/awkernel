use core::arch::x86_64::__cpuid;

use x86_64::registers::model_specific::Msr;

use crate::{
    delay::wait_millisec,
    dvfs::{Dvfs, Error, Result},
};

use super::X86;

#[allow(dead_code)] // TODO: remove this later
mod hwpstate_intel;

const MSR_PLATFORM_INFO: u32 = 0xCE;
const MSR_PLATFORM_INFO_MAX_OFFSET: u32 = 8;
const MSR_PLATFORM_INFO_MIN_OFFSET: u32 = 40;
const IA32_PERF_MPERF: u32 = 0xE7;
const IA32_PERF_APERF: u32 = 0xE8;
const IA32_PERF_CTL: u32 = 0x199;
const IA32_MISC_ENABLE: u32 = 0x1A0;

fn bus_freq_mhz() -> u64 {
    match (__cpuid(0x16).ecx & 0xffff) as u64 {
        0 => 100, // Default to 100 MHz if bus frequency is not reported (old CPUs).
        freq => freq,
    }
}

impl Dvfs for X86 {
    /// Fix the frequency of the current CPU.
    fn set_cpu_freq(freq: u64) -> Result<()> {
        unsafe {
            let mut misc_enable = Msr::new(IA32_MISC_ENABLE);
            let mut value = misc_enable.read();

            // Enable Enhanced Intel SpeedStep Technology
            value |= 1 << 16;

            misc_enable.write(value);
        }

        let bus_freq_mhz = bus_freq_mhz();
        let target_pstate = (freq / bus_freq_mhz / 1_000_000) & 0xFFFF;
        unsafe {
            let mut perf_ctl = Msr::new(IA32_PERF_CTL);
            let mut value = perf_ctl.read();

            // Disable Dynamic Acceleration Technology and Turbo Boost Technology
            value |= 1 << 32;

            // Set target pstate
            value &= !0xFFFF;
            value |= target_pstate;
            perf_ctl.write(value);
        }
        Ok(())
    }

    /// Get the maximum frequency of the current CPU.
    fn get_max_cpu_freq() -> Result<u64> {
        unsafe {
            let platform_info = Msr::new(MSR_PLATFORM_INFO);
            let max_ratio = (platform_info.read() >> MSR_PLATFORM_INFO_MAX_OFFSET) & 0xFF;
            let bus_freq_mhz = bus_freq_mhz();

            Ok(max_ratio * bus_freq_mhz * 1_000_000)
        }
    }

    /// Get the minimum frequency of the current CPU.
    fn get_min_cpu_freq() -> Result<u64> {
        unsafe {
            let platform_info = Msr::new(MSR_PLATFORM_INFO);
            let min_ratio = (platform_info.read() >> MSR_PLATFORM_INFO_MIN_OFFSET) & 0xFF;
            let bus_freq_mhz = bus_freq_mhz();

            Ok(min_ratio * bus_freq_mhz * 1_000_000)
        }
    }

    /// Get the current frequency of the current CPU.
    fn get_curr_cpu_freq() -> Result<u64> {
        // Check if the CPU supports the IA32_PERF_MPERF and IA32_PERF_APERF MSRs.
        let cpuid = __cpuid(0x6);
        if (cpuid.ecx & 0x1) == 0 {
            log::warn!("The CPU does not support IA32_PERF_MPERF and IA32_PERF_APERF MSRs.");
            return Err(Error::NotSupported);
        }

        unsafe {
            let mut mperf = Msr::new(IA32_PERF_MPERF);
            let mut aperf = Msr::new(IA32_PERF_APERF);
            aperf.write(0);
            mperf.write(0);

            wait_millisec(100);

            let mperf_delta = mperf.read();
            let aperf_delta = aperf.read();

            let max_cpu_freq_mhz = Self::get_max_cpu_freq().unwrap() / 1_000_000;

            Ok(aperf_delta * max_cpu_freq_mhz / mperf_delta * 1_000_000)
        }
    }
}
