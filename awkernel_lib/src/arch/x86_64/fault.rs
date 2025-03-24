use core::sync::atomic::{AtomicU32, Ordering};

use array_macro::array;

use crate::cpu::NUM_MAX_CPU;

static NUM_GENERAL_PROTECTION_FAULT: [AtomicU32; NUM_MAX_CPU] =
    array![_ => AtomicU32::new(0); NUM_MAX_CPU];

/// Get the number of general protection fault.
#[inline]
pub fn get_num_general_protection_fault(cpuid: usize) -> u32 {
    NUM_GENERAL_PROTECTION_FAULT[cpuid].load(Ordering::Relaxed)
}

/// Increment the number of general protection fault.
#[inline]
pub fn inc_num_general_protection_fault(cpuid: usize) {
    NUM_GENERAL_PROTECTION_FAULT[cpuid].fetch_add(1, Ordering::Relaxed);
}
