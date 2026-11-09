use super::{rdmsr_safe, wrmsr_safe};
use x86_64::registers::model_specific::Msr;

const MSR_NUMBER: u32 = 0xE7;

#[inline]
pub fn try_read() -> Option<u64> {
    unsafe { rdmsr_safe(&Msr::new(MSR_NUMBER)) }
}

#[inline]
pub fn try_write(value: u64) -> bool {
    unsafe { wrmsr_safe(&mut Msr::new(MSR_NUMBER), value) }
}
/// Reads the IA32_PERF_MPERF MSR without checking for errors.
///
/// # Safety
///
/// The caller must ensure that IA32_PERF_MPERF MSR is available
///
/// # Panics
///
/// Panics with the `std` feature enabled; privileged MSR access is unsupported.
#[inline]
pub unsafe fn read_unchecked() -> u64 {
    #[cfg(feature = "std")]
    panic!("read_unchecked is not supported on std");
    #[cfg(not(feature = "std"))]
    Msr::new(MSR_NUMBER).read()
}

/// Writes the IA32_PERF_MPERF MSR without checking for errors.
///
/// # Safety
///
/// The caller must ensure that IA32_PERF_MPERF MSR is available
///
/// # Panics
///
/// Panics with the `std` feature enabled; privileged MSR access is unsupported.
#[inline]
pub unsafe fn write_unchecked(value: u64) {
    #[cfg(feature = "std")]
    {
        let _ = value;
        panic!("write_unchecked is not supported on std");
    }
    #[cfg(not(feature = "std"))]
    Msr::new(MSR_NUMBER).write(value);
}
