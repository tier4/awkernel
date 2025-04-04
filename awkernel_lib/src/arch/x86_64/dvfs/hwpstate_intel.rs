use core::arch::x86_64::__cpuid;

use array_macro::array;
use awkernel_sync::{mcs::MCSNode, mutex::Mutex};
use x86_64::registers::model_specific::Msr;

use crate::{
    arch::x86_64::msr::*,
    cpu::{cpu_id, NUM_MAX_CPU},
    dvfs::Dvfs,
};

const CPUTPM1_HWP_NOTIFICATION: u32 = 0x00000100;
const CPUTPM1_HWP_ACTIVITY_WINDOW: u32 = 0x00000200;
const CPUTPM1_HWP_PERF_PREF: u32 = 0x00000400;
const CPUTPM1_HWP_PKG: u32 = 0x00000800;
const CPUID_PERF_BIAS: u32 = 0x00000008;

/// Enable/disable pkg-level control.
static HWPSTATE_PKG_CTRL_ENABLE: bool = false;

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
        let hwp_pkg_ctrl_en = hwp_pkg_ctrl && HWPSTATE_PKG_CTRL_ENABLE;

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
                self.req = result;
            } else {
                log::error!("Failed to read HWP request MSR for cpu{}", cpu_id());
                return false;
            }

            let hwp_caps = Msr::new(MSR_IA32_HWP_CAPABILITIES);

            if let Some(result) = rdmsr_safe(&hwp_caps) {
                caps = result;
            } else {
                log::error!("Failed to read HWP capabilities MSR for cpu{}", cpu_id());
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

        if !self.hwp_perf_ctrl && !self.hwp_perf_bias_cached {
            // If cpuid indicates EPP is not supported, the HWP controller
            // uses MSR_IA32_ENERGY_PERF_BIAS instead (Intel SDM Â§14.4.4).
            // This register is per-core (but not HT).
            let msr_ebp = Msr::new(MSR_IA32_ENERGY_PERF_BIAS);
            if let Some(epb) = unsafe { rdmsr_safe(&msr_ebp) } {
                self.hwp_energy_perf_bias = epb;
                self.hwp_perf_bias_cached = true;
            } else {
                return false;
            }
        }

        log::info!(
            "hwpstate_intel: cpu_id = {}, low = {}, high = {}, guaranteed = {}, efficient = {}",
            cpu_id(),
            self.low,
            self.high,
            self.guaranteed,
            self.efficient,
        );

        true
    }

    /// Select Efficiency/Performance Preference.
    /// (range from 0, most performant, through 100, most efficient)
    pub(super) fn epp_select(&mut self, epp: u8) -> bool {
        let epp = if epp > 100 { 100 } else { epp };

        // Disable interrupt to suppress preemption.
        let _int_guard = crate::interrupt::InterruptGuard::new();

        if self.hwp_perf_ctrl {
            let val = percent_to_raw(epp as u64);

            self.req = (self.req & !IA32_HWP_REQUEST_ENERGY_PERFORMANCE_PREFERENCE) | (val << 24);
            self.request()
        } else {
            let val = percent_to_raw_perf_bias(epp as u64);
            self.hwp_energy_perf_bias =
                (self.hwp_energy_perf_bias & !IA32_ENERGY_PERF_BIAS_POLICY_HINT_MASK) | val;

            let mut msr_epb = Msr::new(MSR_IA32_ENERGY_PERF_BIAS);
            unsafe { wrmsr_safe(&mut msr_epb, self.hwp_energy_perf_bias) }
        }
    }

    /// Select Maximum Performance.
    /// (range from 0, lowest performant, through 100, highest performance)
    ///
    /// If `max` is less than the minimum performance,
    /// this function sets the maximum performance to the minimum performance.
    ///
    /// If `max` is greater than 100, it will be treated as 100.
    pub(super) fn maximum_performance_select(&mut self, max: u8) -> bool {
        let raw_max = self.percent_to_raw_performance(max);
        let raw_min = (self.req & IA32_HWP_MINIMUM_PERFORMANCE) as u8;

        let val = (if raw_max < raw_min { raw_min } else { raw_max }) as u64;

        self.req = (self.req & !IA32_HWP_REQUEST_MAXIMUM_PERFORMANCE) | (val << 8);
        self.request()
    }

    /// Select Minimum Performance.
    /// (range from 0, lowest performant, through 100, highest performance)
    ///
    /// If `min` is greater than the maximum performance,
    /// this function sets the minimum performance to the maximum performance.
    ///
    /// If `min` is greater than 100, it will be treated as 100.
    pub(super) fn minimum_performance_select(&mut self, min: u8) -> bool {
        let raw_max = ((self.req & IA32_HWP_REQUEST_MAXIMUM_PERFORMANCE) >> 8) as u8;
        let raw_min = self.percent_to_raw_performance(min);

        let val = (if raw_max < raw_min { raw_max } else { raw_min }) as u64;

        self.req = (self.req & !IA32_HWP_MINIMUM_PERFORMANCE) | val;
        self.request()
    }

    #[inline]
    fn request(&self) -> bool {
        if self.hwp_pkg_ctrl_en {
            let mut hwp_req_pkg = Msr::new(MSR_IA32_HWP_REQUEST_PKG);
            unsafe { wrmsr_safe(&mut hwp_req_pkg, self.req) }
        } else {
            let mut hwp_req = Msr::new(MSR_IA32_HWP_REQUEST);
            unsafe { wrmsr_safe(&mut hwp_req, self.req) }
        }
    }

    /// Returns a raw performance value between `self.low` and `self.high` depending on `percent`.
    /// If `percent` is 0 or 100, this returns `self.low` or `self.high`, respectively.
    /// If `percent` is greater than 100, it will be treated as 100.
    fn percent_to_raw_performance(&self, percent: u8) -> u8 {
        let percent = if percent > 100 { 100 } else { percent };

        // fast return
        if percent == 100 {
            return self.high;
        }

        if percent == 0 {
            return self.low;
        }

        assert!(self.high >= self.low);
        let range = self.high - self.low;

        // To avoid overflow, the raw value is calculated by casting the values to u32.
        let val = (percent as u32 * range as u32) / 100 + self.low as u32;
        if val > self.high as u32 {
            self.high
        } else if val < self.low as u32 {
            self.low
        } else {
            val as u8
        }
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

static HWPSTATE_INTEL: [Mutex<Option<HwPstateIntel>>; NUM_MAX_CPU] =
    array![_ => Mutex::new(None); NUM_MAX_CPU];

pub(super) struct HwPstateIntelImpl;

impl Dvfs for HwPstateIntelImpl {
    fn set_min_performance(min: u8) -> bool {
        let cpu_id = cpu_id();

        let mut node = MCSNode::new();
        let mut hwps = HWPSTATE_INTEL[cpu_id].lock(&mut node);

        if let Some(hwps) = hwps.as_mut() {
            hwps.minimum_performance_select(min)
        } else {
            false
        }
    }

    fn set_max_performance(max: u8) -> bool {
        let cpu_id = cpu_id();

        let mut node = MCSNode::new();
        let mut hwps = HWPSTATE_INTEL[cpu_id].lock(&mut node);

        if let Some(hwps) = hwps.as_mut() {
            hwps.maximum_performance_select(max)
        } else {
            false
        }
    }
}

/// Initialize Intel Hardware-controlled Performance States
/// This function should be called before the main loop on each CPU core.
///
/// # Safety
///
/// This function must be called once by each CPU core.
pub(super) unsafe fn init() -> bool {
    let cpu_id = cpu_id();

    let hwps = &HWPSTATE_INTEL[cpu_id];
    let mut node = MCSNode::new();
    let mut hwps = hwps.lock(&mut node);

    if hwps.is_none() {
        *hwps = HwPstateIntel::new();
    }

    hwps.is_some()
}
