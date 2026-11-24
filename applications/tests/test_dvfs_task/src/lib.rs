#![no_std]

extern crate alloc;

use alloc::vec::Vec;
use core::{
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

use awkernel_async_lib::{
    scheduler::SchedulerType,
    task::{self, TaskResult},
};
use awkernel_lib::{
    cpu::{CpuSet, num_cpu},
    dvfs::{get_curr_cpu_freq, get_max_cpu_freq},
    time::Instant,
};

const NUM_LOOP: usize = 100_000_000;
const NUM_ROUND: usize = 10;
const NUM_TASKS: usize = 3;

/// Number of finished `busy_loop` tasks.
static FINISHED: AtomicUsize = AtomicUsize::new(0);

pub async fn run() {
    if num_cpu() < 7 {
        log::error!("need at least 7 CPUs");
        return;
    }

    let max = match get_max_cpu_freq() {
        Ok(f) => f,
        Err(e) => {
            log::error!("get_max_cpu_freq failed: {e:?}");
            return;
        }
    };

    task::spawn(
        "dvfs_task_none".into(),
        busy_loop(1, None),
        SchedulerType::EDF(1_000_000, CpuSet::empty().with(2)),
    );

    task::spawn_with_freq(
        "dvfs_task_half".into(),
        busy_loop(2, Some(max / 2)),
        SchedulerType::EDF(1_000_000, CpuSet::empty().with(4)),
        max / 2,
    );

    task::spawn_with_freq(
        "dvfs_task_max".into(),
        busy_loop(3, Some(max)),
        SchedulerType::EDF(1_000_000, CpuSet::empty().with(6)),
        max,
    );

    // Wait for all tasks to finish.
    while FINISHED.load(Ordering::Relaxed) < NUM_TASKS {
        awkernel_async_lib::sleep(Duration::from_millis(100)).await;
    }

    // Check that each worker CPU (CPU#0 runs no task) requested the minimum
    // frequency when idle. Read the scheduler's records instead of running a
    // task on each CPU, which would change its frequency. Read them all before
    // logging, because the logger task resets the record of the CPU it runs on.
    let self_cpu = awkernel_lib::cpu::cpu_id();
    let requested: Vec<bool> = (1..num_cpu())
        .map(task::is_idle_min_freq_requested)
        .collect();

    for (core, requested) in (1..num_cpu()).zip(requested) {
        if core == self_cpu {
            log::info!("after all tasks: CPU#{core} is running this test, skipped");
        } else if requested {
            log::info!("after all tasks: CPU#{core} requested the minimum frequency when idle");
        } else {
            log::error!(
                "after all tasks: CPU#{core} did not request the minimum frequency when idle"
            );
        }
    }
}

async fn busy_loop(label: u32, expected: Option<u64>) -> TaskResult {
    for _ in 0..NUM_ROUND {
        // Measure while keeping interrupts (and thus preemption) disabled.
        let int_guard = awkernel_lib::interrupt::InterruptGuard::new();
        let cpuid = awkernel_lib::cpu::cpu_id();
        let start = Instant::now();
        for _ in 0..NUM_LOOP {
            core::hint::black_box(());
        }
        let t = start.elapsed();
        let current = get_curr_cpu_freq();
        drop(int_guard);

        // Log outside the guard.
        match current {
            Ok(current) => log::info!(
                "dvfs_task {label}: CPU#{cpuid}, current = {current}, expected = {expected:?}, time = {t:?}"
            ),
            Err(e) => log::warn!("dvfs_task {label}: get_curr_cpu_freq failed: {e:?}"),
        }

        awkernel_async_lib::r#yield().await;
    }
    log::info!("dvfs_task {label} finished");
    FINISHED.fetch_add(1, Ordering::Relaxed);
    Ok(())
}
