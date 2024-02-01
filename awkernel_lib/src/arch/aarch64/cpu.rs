use crate::cpu::{CPU, NUM_MAX_CPU};
use awkernel_aarch64::mpidr_el1;

#[no_mangle]
pub static mut AFF0_MAX: u64 = 0;

#[no_mangle]
pub static mut AFF1_MAX: u64 = 0;

#[no_mangle]
pub static mut AFF2_MAX: u64 = 0;

static mut AFF0_X_AFF1: u64 = 0;

static mut AFF0_X_AFF1_X_AFF2: u64 = 0;

static mut CPU_LIST: [Option<(u8, u8, u8, u8)>; NUM_MAX_CPU] = [None; NUM_MAX_CPU];

impl CPU for super::AArch64 {
    fn cpu_id() -> usize {
        let mpidr = mpidr_el1::get();

        let aff0 = mpidr & 0xff;
        let aff1 = (mpidr >> 8) & 0xff;
        let aff2 = (mpidr >> 16) & 0xff;
        let aff3 = (mpidr >> 32) & 0xff;

        let result =
            unsafe { aff0 + AFF0_MAX * aff1 + AFF0_X_AFF1 * aff2 + AFF0_X_AFF1_X_AFF2 * aff3 };

        result as usize
    }

    fn raw_cpu_id() -> usize {
        mpidr_el1::get() as usize
    }
}

/// Set the maximum affinity for each affinity level.
///
/// # Safety
///
/// The number of affinity must be calculated during boot.
pub unsafe fn set_max_affinity(aff0_max: u64, aff1_max: u64, aff2_max: u64, aff3_max: u64) {
    AFF0_MAX = aff0_max;
    AFF1_MAX = aff1_max;
    AFF2_MAX = aff2_max;

    AFF0_X_AFF1 = aff0_max * aff1_max;
    AFF0_X_AFF1_X_AFF2 = aff0_max * aff1_max * aff2_max;

    let mut id = 0;
    for aff3 in 0..aff3_max {
        for aff2 in 0..aff2_max {
            for aff1 in 0..aff1_max {
                for aff0 in 0..aff0_max {
                    CPU_LIST[id] = Some((aff0 as u8, aff1 as u8, aff2 as u8, aff3 as u8));
                    id += 1;
                }
            }
        }
    }
}

pub fn get_affinity(cpu_id: usize) -> Option<(u8, u8, u8, u8)> {
    unsafe { CPU_LIST[cpu_id] }
}

pub const AFF3_MASK: u64 = 0xff << 32;
pub const AFF2_MASK: u64 = 0xff << 16;
pub const AFF1_MASK: u64 = 0xff << 8;
pub const AFF0_MASK: u64 = 0xff;

/// Get the current CPU affinity.
pub fn current_affinity() -> (u8, u8, u8, u8) {
    let mpidr_el1 = awkernel_aarch64::mpidr_el1::get();
    (
        ((mpidr_el1 & AFF3_MASK) >> 32) as u8,
        ((mpidr_el1 & AFF2_MASK) >> 16) as u8,
        ((mpidr_el1 & AFF1_MASK) >> 8) as u8,
        (mpidr_el1 & AFF0_MASK) as u8,
    )
}
