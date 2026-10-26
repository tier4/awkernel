//! Work-bound busy execution, calibrated per CPU.
//!
//! [`spin_work`] performs a fixed *amount of computation* rather than spinning
//! until a wall-clock deadline. A wall-clock spin (e.g. [`crate::delay::wait_microsec`])
//! that gets preempted resumes after its deadline has already passed and so
//! finishes having done less work than requested; a work-bound loop does not,
//! because time spent preempted performs no iterations.
//!
//! Iterations-per-millisecond is measured separately on every CPU
//! ([`calibrate_current_cpu`]), so a duration means "that long on an
//! uncontended run of *this* core" even on hybrid (P/E-core) processors, where
//! one shared calibration would make the same work take longer on slower cores.

use core::{
    hint::black_box,
    sync::atomic::{AtomicBool, AtomicU64, Ordering},
    time::Duration,
};

use crate::cpu::NUM_MAX_CPU;

/// Iterations of [`busy_iteration`] per millisecond, per CPU. 0 = not calibrated.
static ITERS_PER_MS: [AtomicU64; NUM_MAX_CPU] = [const { AtomicU64::new(0) }; NUM_MAX_CPU];

static WARNED_UNCALIBRATED: AtomicBool = AtomicBool::new(false);

const CALIBRATION_US: u64 = 5_000;
const SAMPLE_EVERY: u64 = 4096;

/// Work is split into chunks so the per-CPU rate is re-read after a migration.
/// `cpu_id()` costs a few CPUID instructions on x86_64, so a chunk must be long
/// enough to amortize it (~0.3% at 100us); a chunk interrupted by a migration is
/// charged at its starting CPU's rate, an error bounded by one chunk.
const CHUNK_NS: u64 = 100_000;

#[inline(always)]
fn busy_iteration(acc: u64) -> u64 {
    // `black_box` keeps the compiler from proving the loop dead. Deliberately not
    // `spin_loop()`: PAUSE hands execution resources to an SMT sibling.
    black_box(acc.wrapping_mul(2_654_435_761).wrapping_add(1))
}

/// Measure the calling CPU's rate and store it.
///
/// Call once per CPU during boot, after the CPU's frequency is final and before
/// it runs tasks. Interrupts are disabled while measuring.
///
/// The stored rate is measured on the same loop shape [`spin_work`] runs (a
/// `cpu_id()` call per chunk), so that per-chunk cost is part of the rate
/// rather than a bias on top of it. It is large under virtualization, where
/// every CPUID is a VM exit.
pub fn calibrate_current_cpu() -> Option<u64> {
    let cpu = crate::cpu::cpu_id();
    let slot = ITERS_PER_MS.get(cpu)?;

    let _int_guard = crate::interrupt::InterruptGuard::new();

    // Pass 1: raw loop rate, only to size a chunk for pass 2.
    let raw_per_ms = measure_iters_per_ms(None);
    let chunk_iters = (raw_per_ms.saturating_mul(CHUNK_NS) / 1_000_000).max(1);

    let per_ms = measure_iters_per_ms(Some(chunk_iters));
    slot.store(per_ms, Ordering::Relaxed);
    Some(per_ms)
}

/// Iterations per millisecond over [`CALIBRATION_US`]: the bare loop if
/// `chunk_iters` is `None`, otherwise chunks of that size each preceded by a
/// `cpu_id()` call as in [`spin_work`].
fn measure_iters_per_ms(chunk_iters: Option<u64>) -> u64 {
    let start = crate::delay::uptime();
    let mut acc: u64 = 1;
    let mut iters: u64 = 0;

    let elapsed = loop {
        match chunk_iters {
            None => {
                for _ in 0..SAMPLE_EVERY {
                    acc = busy_iteration(acc);
                }
                iters = iters.saturating_add(SAMPLE_EVERY);
            }
            Some(n) => {
                black_box(crate::cpu::cpu_id());
                for _ in 0..n {
                    acc = busy_iteration(acc);
                }
                iters = iters.saturating_add(n);
            }
        }

        let elapsed = crate::delay::uptime().saturating_sub(start);
        if elapsed >= CALIBRATION_US {
            break elapsed;
        }
    };
    black_box(acc);

    (iters.saturating_mul(1000) / elapsed.max(1)).max(1)
}

/// Calibrated rate of `cpu_id`, or `None` if it has not been calibrated.
pub fn iters_per_ms(cpu_id: usize) -> Option<u64> {
    let v = ITERS_PER_MS.get(cpu_id)?.load(Ordering::Relaxed);
    (v != 0).then_some(v)
}

/// Perform `duration` worth of computation as measured by [`calibrate_current_cpu`].
///
/// On a CPU that was never calibrated this falls back to a wall-clock wait for
/// the remainder (and logs a warning once), since doing no work at all would be
/// worse.
pub fn spin_work(duration: Duration) {
    let mut remaining_ns = u64::try_from(duration.as_nanos()).unwrap_or(u64::MAX);
    let mut acc: u64 = 1;

    while remaining_ns > 0 {
        let step_ns = remaining_ns.min(CHUNK_NS);

        let Some(per_ms) = iters_per_ms(crate::cpu::cpu_id()) else {
            if !WARNED_UNCALIBRATED.swap(true, Ordering::Relaxed) {
                log::warn!(
                    "busy_work: CPU#{} is not calibrated; falling back to a wall-clock wait",
                    crate::cpu::cpu_id()
                );
            }
            crate::delay::wait_microsec(remaining_ns.div_ceil(1000));
            return;
        };

        let iters = per_ms.saturating_mul(step_ns) / 1_000_000;
        for _ in 0..iters {
            acc = busy_iteration(acc);
        }

        remaining_ns -= step_ns;
    }

    black_box(acc);
}
