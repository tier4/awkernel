use core::{
    arch::x86_64::{_mm_mfence, _rdtsc},
    sync::atomic::{AtomicU64, Ordering},
};

use x86_64::registers::model_specific::Msr;

use crate::{
    addr::{virt_addr::VirtAddr, Addr},
    arch::x86_64::kvm::KvmCpuidFeatures,
};

const MSR_KVM_SYSTEM_TIME_NEW: u32 = 0x4b564d01;
const PVCLOCK_FLAG_TSC_STABLE: u8 = 0x01;

#[derive(Debug)]
#[repr(C)]
struct VcpuTimeInfo {
    version: u32,
    pad0: u32,
    tsc_timestamp: u64,
    system_time: u64,
    tsc_to_system_mul: u32,
    tsc_shift: i8,
    flags: u8,
    pad: [u8; 2],
}

static VCPU_TIME_INFO: VcpuTimeInfo = VcpuTimeInfo {
    version: 0,
    pad0: 0,
    tsc_timestamp: 0,
    system_time: 0,
    tsc_to_system_mul: 0,
    tsc_shift: 0,
    flags: 0,
    pad: [0; 2],
};

static PVCLOCK_LAST_COUNT: AtomicU64 = AtomicU64::new(0);

/// Retrieves the current system time within a KVM virtual machine.
///
/// This function attempts to read the system time from the virtual CPU's time information
/// structure. It first checks if the code is running within a KVM environment and if
/// the necessary CPUID features for accessing the time information are present.
///
/// # Returns
///
/// * `Some(u64)`: The current system time in nanoseconds, if the function successfully
///     retrieved it from a KVM environment with the necessary features.
/// * `None`: If the code is not running in a KVM environment or if the required
///     CPUID features are not available.
#[inline(always)]
pub fn get_system_time() -> Option<u64> {
    if !super::is_kvm() {
        return None;
    }

    if !super::cpuid_features()?
        .contains(KvmCpuidFeatures::CLOCKSOURCE2 | KvmCpuidFeatures::CLOCSOURCE_STABLE_BIT)
    {
        return None;
    }

    if VCPU_TIME_INFO.version == 0 {
        let virt_addr = VirtAddr::new(&VCPU_TIME_INFO as *const _ as _);
        let phy_addr = crate::paging::vm_to_phy(virt_addr)?;

        let mut system_time = Msr::new(MSR_KVM_SYSTEM_TIME_NEW);
        unsafe { system_time.write(phy_addr.as_usize() as u64 | 1) };
    }

    let mut system_time;
    let mut tsc_timestamp;
    let mut mul_frac;
    let mut shift;
    let mut flags;
    let mut version;

    loop {
        version = pvclock_read_begin();

        system_time = VCPU_TIME_INFO.system_time;
        tsc_timestamp = VCPU_TIME_INFO.tsc_timestamp;
        mul_frac = VCPU_TIME_INFO.tsc_to_system_mul;
        shift = VCPU_TIME_INFO.tsc_shift;
        flags = VCPU_TIME_INFO.flags;

        if pvclock_read_done(version) {
            break;
        }
    }

    let mut delta = unsafe { _rdtsc() } - tsc_timestamp;
    if shift < 0 {
        delta >>= -shift;
    } else {
        delta <<= shift;
    }
    let ctr = ((delta as u128 * mul_frac as u128) >> 32) as u64 + system_time;

    if (flags & PVCLOCK_FLAG_TSC_STABLE) != 0 {
        return Some(ctr);
    }

    if let Err(prev) = PVCLOCK_LAST_COUNT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| {
        if n < ctr {
            Some(ctr)
        } else {
            None
        }
    }) {
        Some(prev)
    } else {
        Some(ctr)
    }
}

#[inline(always)]
fn pvclock_read_begin() -> u32 {
    let ver = VCPU_TIME_INFO.version;
    unsafe { _mm_mfence() };
    ver
}

#[inline(always)]
fn pvclock_read_done(version: u32) -> bool {
    unsafe { _mm_mfence() };
    version == VCPU_TIME_INFO.version
}
