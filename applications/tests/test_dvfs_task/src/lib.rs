#![no_std]

extern crate alloc;

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
    dvfs::{get_curr_cpu_freq, get_max_cpu_freq, get_min_cpu_freq},
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

    // Measure the frequency of each worker CPU, one by one.
    // CPU#0 is the primary CPU and does not run tasks.
    let min = get_min_cpu_freq();
    for core in 1..num_cpu() {
        let handle = awkernel_async_lib::spawn(
            "dvfs_task_measure".into(),
            async move {
                match get_curr_cpu_freq() {
                    Ok(f) => log::info!("after all tasks: CPU#{core} = {f} Hz (min = {min:?})"),
                    Err(e) => log::warn!("after all tasks: CPU#{core}: {e:?}"),
                }
            },
            SchedulerType::EDF(1_000_000, CpuSet::empty().with(core)),
        )
        .await;
        let _ = handle.join().await;
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
