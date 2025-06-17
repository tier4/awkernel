use core::arch::x86_64::__cpuid;

use x86_64::registers::model_specific::Msr;

use crate::{delay::wait_millisec, dvfs::Dvfs};

use super::{
    cpu::{self, CPUVendor},
    X86,
};

#[allow(dead_code)] // TODO: remove this later
mod hwpstate_intel;

const MSR_PLATFORM_INFO: u32 = 0xCE;
const IA32_PERF_MPERF: u32 = 0xE7;
const IA32_PERF_APERF: u32 = 0xE8;
const IA32_PERF_CTL: u32 = 0x199;
const IA32_MISC_ENABLE: u32 = 0x1A0;

impl Dvfs for X86 {
    /// Fix the frequency of the current CPU.
    fn fix_freq(freq_mhz: u64) -> bool {
        unsafe {
            let mut misc_enable = Msr::new(IA32_MISC_ENABLE);
            let mut value = misc_enable.read();

            // Enable Enhanced Intel SpeedStep Technology
            value |= 1 << 16;

            misc_enable.write(value);
        }

        let cpuid = unsafe { __cpuid(0x16) };
        let bus_freq_mhz = (cpuid.ecx & 0xffff) as u64;
        let target_pstate = ((freq_mhz / bus_freq_mhz) as u64) & 0xFFFF;
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

        true
    }

    /// Get the maximum frequency of the current CPU.
    fn get_max_freq() -> Option<u64> {
        unsafe {
            let platform_info = Msr::new(MSR_PLATFORM_INFO);
            let max_ratio = (platform_info.read() >> 8) & 0xFF;
            let bus_freq_mhz = (__cpuid(0x16).ecx & 0xffff) as u64;

            Some(max_ratio * bus_freq_mhz)
        }
    }

    /// Get the current frequency of the current CPU.
    fn get_curr_freq() -> Option<u64> {
        // Check if the CPU supports the IA32_PERF_MPERF and IA32_PERF_APERF MSRs.
        let cpuid = unsafe { __cpuid(0x6) };
        if (cpuid.ecx & 0x1) == 0 {
            log::warn!("The CPU does not support IA32_PERF_MPERF and IA32_PERF_APERF MSRs.");
            return None;
        }

        unsafe {
            let mut mperf = Msr::new(IA32_PERF_MPERF);
            let mut aperf = Msr::new(IA32_PERF_APERF);
            aperf.write(0);
            mperf.write(0);

            wait_millisec(100);

            let mperf_delta = mperf.read();
            let aperf_delta = aperf.read();

            Some(aperf_delta * Self::get_max_freq()? / mperf_delta)
        }
    }

    fn set_min_performance(min: u8) -> bool {
        hwpstate_intel::HwPstateIntelImpl::set_min_performance(min)
    }

    fn set_max_performance(max: u8) -> bool {
        hwpstate_intel::HwPstateIntelImpl::set_max_performance(max)
    }

    fn set_desired_performance(val: crate::dvfs::DesiredPerformance) -> bool {
        hwpstate_intel::HwPstateIntelImpl::set_desired_performance(val)
    }

    fn set_min_max_performance(min: u8) -> bool {
        hwpstate_intel::HwPstateIntelImpl::set_min_max_performance(min)
    }
}

/// Initialize DVFS.
///
/// # Safety
///
/// This function must be called once by each CPU core.
pub unsafe fn init() {
    if let Some(CPUVendor::Intel) = cpu::get_cpu_vendor() {
        if !hwpstate_intel::init() {
            log::warn!("Failed to initialize Intel Hardware-controlled Performance States.");
        }
    }
}
