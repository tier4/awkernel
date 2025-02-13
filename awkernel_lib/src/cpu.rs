use crate::arch::ArchImpl;
use core::sync::atomic::{AtomicUsize, Ordering};

pub const NUM_MAX_CPU: usize = 512;
static NUM_CPU: AtomicUsize = AtomicUsize::new(0);

pub trait CPU {
    /// CPU ID returns the ID of the CPU.
    /// The ID is unique for each CPU and starts from 0 to `num_cpu() - 1`.
    fn cpu_id() -> usize;

    /// Raw CPU ID returns the ID of the CPU without any modification.
    fn raw_cpu_id() -> usize;
}

#[inline(always)]
pub fn cpu_id() -> usize {
    ArchImpl::cpu_id()
}

#[inline(always)]
pub fn raw_cpu_id() -> usize {
    ArchImpl::raw_cpu_id()
}

/// # Safety
///
/// This function must be called during the kernel initialization.
pub unsafe fn set_num_cpu(num_cpu: usize) {
    NUM_CPU.store(num_cpu, Ordering::Relaxed);
}

#[inline(always)]
pub fn num_cpu() -> usize {
    NUM_CPU.load(Ordering::Relaxed)
}
