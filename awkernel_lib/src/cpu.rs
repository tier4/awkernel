use crate::arch::ArchCPU;
use core::sync::atomic::{AtomicUsize, Ordering};

pub const NUM_MAX_CPU: usize = 512;
static NUM_CPU: AtomicUsize = AtomicUsize::new(0);

pub trait CPU {
    fn cpu_id() -> usize;
}

pub fn cpu_id() -> usize {
    ArchCPU::cpu_id()
}

/// # Safety
///
/// Each CPU must call this function only once at its entry.
pub unsafe fn increment_num_cpu() {
    NUM_CPU.fetch_add(1, Ordering::Relaxed);
}

pub fn num_cpu() -> usize {
    NUM_CPU.load(Ordering::Relaxed)
}
