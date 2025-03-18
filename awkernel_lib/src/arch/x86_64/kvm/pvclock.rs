use core::{
    alloc::{GlobalAlloc, Layout},
    arch::x86_64::_mm_mfence,
    sync::atomic::{AtomicU64, AtomicUsize, Ordering},
};

use x86_64::registers::model_specific::Msr;

use crate::{
    addr::{virt_addr::VirtAddr, Addr},
    arch::x86_64::{delay::read_tsc, kvm::KvmCpuidFeatures},
    paging::{self, PAGESIZE},
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

static PVCLOCK_LAST_COUNT: AtomicU64 = AtomicU64::new(0);
static MEM_ADDR: AtomicUsize = AtomicUsize::new(0);
static SYSTEM_TIME_START: AtomicU64 = AtomicU64::new(0);

pub fn init() -> Result<(), &'static str> {
    if !available() {
        return Err("pvclock: not available");
    }

    let ptr =
        unsafe { crate::heap::TALLOC.alloc_zeroed(Layout::from_size_align(PAGESIZE, 4).unwrap()) };
    let virt_addr = VirtAddr::new(ptr as _);

    let phy_addr = paging::vm_to_phy(virt_addr).ok_or("pvclock: failed vm_to_phy")?;

    unsafe {
        paging::unmap(virt_addr);
        paging::map(
            virt_addr,
            phy_addr,
            paging::Flags {
                execute: false,
                write: true,
                cache: false,
                write_through: false,
                device: true,
            },
        )
        .or(Err("pvclock: failed to map"))?;
    }

    let mut system_time = Msr::new(MSR_KVM_SYSTEM_TIME_NEW);
    unsafe { system_time.write(phy_addr.as_usize() as u64 | 1) };

    MEM_ADDR.store(virt_addr.as_usize(), Ordering::Relaxed);

    let system_time = get_system_time().ok_or("pvclock: failed to get system time")?;
    SYSTEM_TIME_START.store(system_time, Ordering::Relaxed);

    Ok(())
}

/// Retrieves the current system time within a KVM virtual machine.
///
/// This function attempts to read the system time from the virtual CPU's time information
/// structure. It first checks if the code is running within a KVM environment and if
/// the necessary CPUID features for accessing the time information are present.
///
/// # Returns
///
/// * `Some(u64)`: The current system time in nanoseconds, if the function successfully
///   retrieved it from a KVM environment with the necessary features.
/// * `None`: If the code is not running in a KVM environment or if the required
///   CPUID features are not available.
#[inline(always)]
pub fn get_system_time() -> Option<u64> {
    if !available() {
        return None;
    }

    let ptr = MEM_ADDR.load(Ordering::Relaxed);
    if ptr == 0 {
        return None;
    }

    let info = unsafe { &*(ptr as *mut VcpuTimeInfo) };

    let mut system_time;
    let mut tsc_timestamp;
    let mut mul_frac;
    let mut shift;
    let mut flags;
    let mut version;

    loop {
        version = pvclock_read_begin(info);

        system_time = info.system_time;
        tsc_timestamp = info.tsc_timestamp;
        mul_frac = info.tsc_to_system_mul;
        shift = info.tsc_shift;
        flags = info.flags;

        if pvclock_read_done(info, version) {
            break;
        }
    }

    let mut delta = read_tsc() - tsc_timestamp;
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
fn pvclock_read_begin(info: &VcpuTimeInfo) -> u32 {
    let ver = info.version;
    unsafe { _mm_mfence() };
    ver
}

#[inline(always)]
fn pvclock_read_done(info: &VcpuTimeInfo, version: u32) -> bool {
    unsafe { _mm_mfence() };
    version == info.version
}

#[inline(always)]
pub fn available() -> bool {
    if !super::is_kvm() {
        return false;
    }

    let Some(features) = super::cpuid_features() else {
        return false;
    };

    if !features.contains(KvmCpuidFeatures::CLOCKSOURCE2 | KvmCpuidFeatures::CLOCSOURCE_STABLE_BIT)
    {
        return false;
    }

    true
}

#[inline(always)]
pub(crate) fn uptime_nano() -> u64 {
    let now = get_system_time().unwrap_or_default();
    let start = SYSTEM_TIME_START.load(Ordering::Relaxed);

    now.saturating_sub(start)
}
