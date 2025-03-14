use core::arch::x86_64::__cpuid;

const CPUTPM1_HWP_NOTIFICATION: u32 = 0x00000100;
const CPUTPM1_HWP_ACTIVITY_WINDOW: u32 = 0x00000200;
const CPUTPM1_HWP_PERF_PREF: u32 = 0x00000400;
const CPUTPM1_HWP_PKG: u32 = 0x00000800;
const CPUID_PERF_BIAS: u32 = 0x00000008;

pub(super) struct HwPstateIntel {
    hwp_notifications: bool,
    hwp_activity_window: bool,
    hwp_perf_pref: bool,
    hwp_pkg_ctrl: bool,
    hwp_perf_bias: bool,
}

impl HwPstateIntel {
    pub(super) fn new() -> Option<Self> {
        let cpuid = unsafe { __cpuid(6) };

        let hwp_notifications = cpuid.eax & CPUTPM1_HWP_NOTIFICATION != 0;
        let hwp_activity_window = cpuid.eax & CPUTPM1_HWP_ACTIVITY_WINDOW != 0;
        let hwp_perf_pref = cpuid.eax & CPUTPM1_HWP_PERF_PREF != 0;
        let hwp_pkg_ctrl = cpuid.eax & CPUTPM1_HWP_PKG != 0;

        let hwp_perf_bias = cpuid.ecx & CPUID_PERF_BIAS != 0;

        let mut hwpstate = Self {
            hwp_notifications,
            hwp_activity_window,
            hwp_perf_pref,
            hwp_pkg_ctrl,
            hwp_perf_bias,
        };

        hwpstate.set_autonomous_hwp().then_some(())?;

        Some(hwpstate)
    }

    fn set_autonomous_hwp(&mut self) -> bool {
        todo!();
    }
}
