use x86_64::registers::model_specific::Msr;

use super::fault::get_num_general_protection_fault;

// MSR IA32_HWP_REQUEST
pub(super) const _IA32_HWP_REQUEST_MINIMUM_VALID: u64 = 1 << 63;
pub(super) const _IA32_HWP_REQUEST_MAXIMUM_VALID: u64 = 1 << 62;
pub(super) const _IA32_HWP_REQUEST_DESIRED_VALID: u64 = 1 << 61;
pub(super) const _IA32_HWP_REQUEST_EPP_VALID: u64 = 1 << 60;
pub(super) const _IA32_HWP_REQUEST_ACTIVITY_WINDOW_VALID: u64 = 1 << 59;
pub(super) const IA32_HWP_REQUEST_PACKAGE_CONTROL: u64 = 1 << 42;
pub(super) const IA32_HWP_ACTIVITY_WINDOW: u64 = 0x3ff << 32;
pub(super) const _IA32_HWP_REQUEST_ENERGY_PERFORMANCE_PREFERENCE: u64 = 0xff << 24;
pub(super) const IA32_HWP_DESIRED_PERFORMANCE: u64 = 0xff << 16;
pub(super) const IA32_HWP_REQUEST_MAXIMUM_PERFORMANCE: u64 = 0xff << 8;
pub(super) const IA32_HWP_MINIMUM_PERFORMANCE: u64 = 0xff;

pub(super) const MSR_IA32_PM_ENABLE: u32 = 0x770;
pub(super) const MSR_IA32_HWP_CAPABILITIES: u32 = 0x771;
pub(super) const MSR_IA32_HWP_REQUEST_PKG: u32 = 0x772;
pub(super) const MSR_IA32_HWP_REQUEST: u32 = 0x774;

// MSR IA32_HWP_CAPABILITIES
pub(super) const IA32_HWP_CAPABILITIES_HIGHEST_PERFORMANCE: fn(u64) -> u8 =
    |x| ((x >> 0) & 0xff) as u8;
pub(super) const IA32_HWP_CAPABILITIES_GUARANTEED_PERFORMANCE: fn(u64) -> u8 =
    |x| ((x >> 8) & 0xff) as u8;
pub(super) const IA32_HWP_CAPABILITIES_EFFICIENT_PERFORMANCE: fn(u64) -> u8 =
    |x| ((x >> 16) & 0xff) as u8;
pub(super) const IA32_HWP_CAPABILITIES_LOWEST_PERFORMANCE: fn(u64) -> u8 =
    |x| ((x >> 24) & 0xff) as u8;

/// Read 64 bits msr register.
/// If the `msr` is not supported on your environments, this function returns `false`.
///
/// # Safety
///
/// The caller must ensure that this read operation has no unsafe side effects.
pub unsafe fn rdmsr_safe(msr: &Msr) -> Option<u64> {
    let _int_guard = crate::interrupt::InterruptGuard::new();

    let cpuid = crate::cpu::cpu_id();
    let num_fault1 = get_num_general_protection_fault(cpuid);

    let result = unsafe { msr.read() };

    let num_fault2 = get_num_general_protection_fault(cpuid);

    if num_fault1 != num_fault2 {
        None
    } else {
        Some(result)
    }
}

/// Write 64 bits to msr register.
/// If the `msr` is not supported on your environments, this function returns `false`.
///
/// # Safety
///
/// The caller must ensure that this write operation has no unsafe side effects.
pub unsafe fn wrmsr_safe(msr: &mut Msr, value: u64) -> bool {
    let _int_guard = crate::interrupt::InterruptGuard::new();

    let cpuid = crate::cpu::cpu_id();
    let num_fault1 = get_num_general_protection_fault(cpuid);

    unsafe { msr.write(value) };

    let num_fault2 = get_num_general_protection_fault(cpuid);

    num_fault1 == num_fault2
}
