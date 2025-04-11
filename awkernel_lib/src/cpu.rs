use crate::arch::ArchImpl;
use core::sync::atomic::{AtomicUsize, Ordering};

pub const NUM_MAX_CPU: usize = 512;
static NUM_CPU: AtomicUsize = AtomicUsize::new(0);

#[cfg(feature = "std")]
mod sleep_cpu_std;

#[cfg(feature = "std")]
use sleep_cpu_no_std::SleepCpuStd as SleepCpuImpl;

#[cfg(not(feature = "std"))]
mod sleep_cpu_no_std;

#[cfg(not(feature = "std"))]
use sleep_cpu_no_std::SleepCpuNoStd as SleepCpuImpl;

static SLEEP_CPU_IMPL: SleepCpuImpl = SleepCpuImpl;

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

pub trait SleepCpu {
    /// Sleep current CPU.
    fn sleep(&self);

    /// Wake up the CPU.
    fn wake_up(cpu_id: usize);
}

/// Sleep the current CPU.
pub fn sleep_cpu() {
    SLEEP_CPU_IMPL.sleep();
}

/// Wake up the CPU with the given `cpu_id`.
pub fn wake_cpu(cpu_id: usize) {
    SleepCpuImpl::wake_up(cpu_id);
}
