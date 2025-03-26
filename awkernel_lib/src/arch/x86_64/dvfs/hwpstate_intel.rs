use core::arch::x86_64::__cpuid;

use x86_64::registers::model_specific::Msr;

use crate::{arch::x86_64::msr::*, cpu::cpu_id};

const CPUTPM1_HWP_NOTIFICATION: u32 = 0x00000100;
const CPUTPM1_HWP_ACTIVITY_WINDOW: u32 = 0x00000200;
const CPUTPM1_HWP_PERF_PREF: u32 = 0x00000400;
const CPUTPM1_HWP_PKG: u32 = 0x00000800;
const CPUID_PERF_BIAS: u32 = 0x00000008;

pub(super) struct HwPstateIntel {
    hwp_notifications: bool,
    hwp_activity_window: bool,
    hwp_perf_ctrl: bool,
    hwp_pkg_ctrl: bool,
    hwp_pkg_ctrl_en: bool,
    hwp_perf_bias: bool,

    hwp_energy_perf_bias: u64,
    hwp_perf_bias_cached: bool,

    high: u8,
    guaranteed: u8,
    efficient: u8,
    low: u8,

    req: u64,
}

impl HwPstateIntel {
    pub(super) fn new() -> Option<Self> {
        let cpuid = unsafe { __cpuid(6) };

        let hwp_notifications = cpuid.eax & CPUTPM1_HWP_NOTIFICATION != 0;
        let hwp_activity_window = cpuid.eax & CPUTPM1_HWP_ACTIVITY_WINDOW != 0;
        let hwp_perf_ctrl = cpuid.eax & CPUTPM1_HWP_PERF_PREF != 0;
        let hwp_pkg_ctrl = cpuid.eax & CPUTPM1_HWP_PKG != 0;

        // Allow administrators to disable pkg-level control.
        let hwp_pkg_ctrl_en = hwp_pkg_ctrl;

        let hwp_perf_bias = cpuid.ecx & CPUID_PERF_BIAS != 0;

        let mut hwpstate = Self {
            hwp_notifications,
            hwp_activity_window,
            hwp_perf_ctrl,
            hwp_pkg_ctrl,
            hwp_pkg_ctrl_en,
            hwp_perf_bias,

            hwp_energy_perf_bias: 0,
            hwp_perf_bias_cached: false,

            high: 0,
            guaranteed: 0,
            efficient: 0,
            low: 0,

            req: 0,
        };

        hwpstate.set_autonomous_hwp().then_some(())?;

        Some(hwpstate)
    }

    fn set_autonomous_hwp(&mut self) -> bool {
        // Disable interrupt to suppress preemption.
        let _int_guard = crate::interrupt::InterruptGuard::new();

        let mut hwp_req = Msr::new(MSR_IA32_HWP_REQUEST);

        // Many MSRs aren't readable until feature is enabled
        let caps;
        unsafe {
            let mut pm_enable = Msr::new(MSR_IA32_PM_ENABLE);

            if !wrmsr_safe(&mut pm_enable, 1) {
                log::error!("Failed to enable HWP for cpu{}", cpu_id());
                return false;
            }

            if let Some(result) = rdmsr_safe(&hwp_req) {
                log::error!("Failed to read HWP request MSR for cpu{}", cpu_id());
                self.req = result;
            } else {
                return false;
            }

            let hwp_caps = Msr::new(MSR_IA32_HWP_CAPABILITIES);

            if let Some(result) = rdmsr_safe(&hwp_caps) {
                log::error!("Failed to read HWP capabilities MSR for cpu{}", cpu_id());
                caps = result;
            } else {
                return false;
            }
        }

        // High and low are static; "guaranteed" is dynamic; and efficient is
        // also dynamic.
        self.high = IA32_HWP_CAPABILITIES_HIGHEST_PERFORMANCE(caps);
        self.guaranteed = IA32_HWP_CAPABILITIES_GUARANTEED_PERFORMANCE(caps);
        self.efficient = IA32_HWP_CAPABILITIES_EFFICIENT_PERFORMANCE(caps);
        self.low = IA32_HWP_CAPABILITIES_LOWEST_PERFORMANCE(caps);

        // hardware autonomous selection determines the performance target
        self.req &= !IA32_HWP_DESIRED_PERFORMANCE;

        // enable HW dynamic selection of window size
        self.req &= !IA32_HWP_ACTIVITY_WINDOW;

        // IA32_HWP_REQUEST.Minimum_Performance = IA32_HWP_CAPABILITIES.Lowest_Performance
        self.req &= !IA32_HWP_MINIMUM_PERFORMANCE;
        self.req |= self.low as u64;

        // IA32_HWP_REQUEST.Maximum_Performance = IA32_HWP_CAPABILITIES.Highest_Performance.
        self.req &= !IA32_HWP_REQUEST_MAXIMUM_PERFORMANCE;
        self.req |= (self.high as u64) << 8;

        // If supported, request package-level control for this CPU.
        let result = unsafe {
            if self.hwp_pkg_ctrl_en {
                wrmsr_safe(&mut hwp_req, self.req | IA32_HWP_REQUEST_PACKAGE_CONTROL)
            } else {
                wrmsr_safe(&mut hwp_req, self.req)
            }
        };

        if !result {
            log::error!(
                "Failed to setup{} autonomous HWP for cpu{}",
                if self.hwp_pkg_ctrl_en { " PKG" } else { "" },
                cpu_id()
            );
            return false;
        }

        // If supported, write the PKG-wide control MSR.
        if self.hwp_pkg_ctrl_en {
            // "The structure of the IA32_HWP_REQUEST_PKG MSR
            // (package-level) is identical to the IA32_HWP_REQUEST MSR
            // with the exception of the Package Control field, which does
            // not exist." (Intel SDM Â§14.4.4)

            let mut hwp_req_pkg = Msr::new(MSR_IA32_HWP_REQUEST_PKG);

            let result = unsafe { wrmsr_safe(&mut hwp_req_pkg, self.req) };
            if !result {
                log::error!("Failed to setup autonomous HWP for package");
                return false;
            }
        }

        true
    }

    /// Select Efficiency/Performance Preference.
    /// (range from 0, most performant, through 100, most efficient)
    pub(super) fn epp_select(&mut self, epp: u8) -> bool {
        let epp = if epp > 100 { 100 } else { epp };

        // Disable interrupt to suppress preemption.
        let _int_guard = crate::interrupt::InterruptGuard::new();

        let mut val;

        if self.hwp_perf_ctrl {
            val = (self.req & IA32_HWP_REQUEST_ENERGY_PERFORMANCE_PREFERENCE) >> 24;
            val = raw_to_percent(val);
        } else {
            // If cpuid indicates EPP is not supported, the HWP controller
            // uses MSR_IA32_ENERGY_PERF_BIAS instead (Intel SDM Â§14.4.4).
            // This register is per-core (but not HT).
            if !self.hwp_perf_bias_cached {
                let msr_ebp = Msr::new(MSR_IA32_ENERGY_PERF_BIAS);
                if let Some(epb) = unsafe { rdmsr_safe(&msr_ebp) } {
                    self.hwp_energy_perf_bias = epb;
                    self.hwp_perf_bias_cached = true;
                } else {
                    return false;
                }
            }

            val = self.hwp_energy_perf_bias & IA32_ENERGY_PERF_BIAS_POLICY_HINT_MASK;
            val = raw_to_percent_perf_bias(val);
        }

        assert!(val <= 100);

        if self.hwp_perf_ctrl {
            let val = percent_to_raw(epp as u64);

            self.req = (self.req & !IA32_HWP_REQUEST_ENERGY_PERFORMANCE_PREFERENCE) | (val << 24);

            if self.hwp_pkg_ctrl_en {
                let mut hwp_req_pkg = Msr::new(MSR_IA32_HWP_REQUEST_PKG);
                if !unsafe { wrmsr_safe(&mut hwp_req_pkg, self.req) } {
                    return false;
                }
            } else {
                let mut hwp_req = Msr::new(MSR_IA32_HWP_REQUEST);
                if !unsafe { wrmsr_safe(&mut hwp_req, self.req) } {
                    return false;
                }
            }
        } else {
            let val = percent_to_raw_perf_bias(epp as u64);
            self.hwp_energy_perf_bias =
                (self.hwp_energy_perf_bias & !IA32_ENERGY_PERF_BIAS_POLICY_HINT_MASK) | val;

            let mut msr_epb = Msr::new(MSR_IA32_ENERGY_PERF_BIAS);
            if !unsafe { wrmsr_safe(&mut msr_epb, self.hwp_energy_perf_bias) } {
                return false;
            }
        }

        true
    }
}

/// Given x * 10 in [0, 1000], round to the integer nearest x.
///
/// This allows round-tripping nice human readable numbers through this
/// interface.  Otherwise, user-provided percentages such as 25, 50, 75 get
/// rounded down to 24, 49, and 74, which is a bit ugly.
fn round10(xtimes10: u64) -> u64 {
    (xtimes10 + 5) / 10
}

fn raw_to_percent(x: u64) -> u64 {
    assert!(x <= 100);
    round10(x * 1000 / 0xff)
}

fn raw_to_percent_perf_bias(x: u64) -> u64 {
    assert!(x <= 0xf);
    ((x * 20) / 0xf) * 5
}

fn percent_to_raw(x: u64) -> u64 {
    assert!(x <= 100);
    0xff * x / 100
}

/// Range of MSR_IA32_ENERGY_PERF_BIAS is more limited: 0-0xf.
fn percent_to_raw_perf_bias(x: u64) -> u64 {
    assert!(x <= 100);
    ((0xf * x) + 50) / 100
}
