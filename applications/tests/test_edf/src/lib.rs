#![no_std]

extern crate alloc;
use alloc::string::String;
use alloc::string::ToString;

use awkernel_async_lib::sleep;
use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{
    cpu::{all_workers, cpu_id, num_cpu, CpuSet},
    delay::{uptime, wait_microsec},
};
use core::{
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

pub async fn run() {
    wait_microsec(2_000_000);

    if num_cpu() < 2 {
        log::warn!("test_edf: requires at least 2 CPUs, skipping");
        return;
    }

    test_global_edf().await;
    test_core_pinning().await;
    test_cluster_affinity().await;
    test_edf_preemption().await;
    test_multi_core().await;
    test_empty_set_fallback().await;

    wait_microsec(100_000_000);
}

/// Number of `test_global_edf` filler tasks that finished their job.
static GLOBAL_FILLERS_DONE: AtomicUsize = AtomicUsize::new(0);

/// Test 0: Verify global EDF (`CpuSet::all()`).
/// One filler per worker core keeps every worker busy, and the userland task
/// (PrioritizedFIFO) is preempted, so no worker is idle. `urgent` wakes from
/// its sleep while the fillers run and must preempt one of them, which means
/// that it runs before any filler finishes. No task may run on CPU 0.
async fn test_global_edf() {
    log::info!("=== test_global_edf start ===");

    spawn(
        "global_urgent".into(),
        async move {
            sleep(Duration::from_millis(200)).await;
            let actual = cpu_id();
            let done = GLOBAL_FILLERS_DONE.load(Ordering::Relaxed);
            if actual != 0 && done == 0 {
                log::info!("global_edf: urgent preempted a filler on cpu {actual} [OK]");
            } else {
                log::error!(
                    "global_edf: urgent ran on cpu {actual} after {done} fillers finished [FAIL]"
                );
            }
        },
        SchedulerType::EDF(300_000, CpuSet::all()),
    )
    .await;

    for i in 1..num_cpu() {
        spawn(
            alloc::format!("global_filler{i}").into(),
            async move {
                let actual = cpu_id();
                if actual == 0 {
                    log::error!("global_edf: filler {i} ran on cpu 0 [FAIL]");
                }
                wait_microsec(1_000_000);
                GLOBAL_FILLERS_DONE.fetch_add(1, Ordering::Relaxed);
            },
            SchedulerType::EDF(10_000_000, CpuSet::all()),
        )
        .await;
    }
}

/// Test 1: Verify tasks are pinned to their assigned cores.
/// Spawns one periodic task per worker core (1..num_cpu()) with a
/// single-core CPU set. Each task checks cpu_id() matches the assigned core.
async fn test_core_pinning() {
    log::info!("=== test_core_pinning start ===");
    for core in 1..num_cpu() {
        spawn(
            alloc::format!("pinning_core{core}").into(),
            async move {
                for _ in 0..3 {
                    let actual = cpu_id();
                    if actual == core {
                        log::info!("core_pinning: task on core {core} ran on cpu {actual} [OK]");
                    } else {
                        log::error!("core_pinning: task on core {core} ran on cpu {actual} [FAIL]");
                    }
                    wait_microsec(100_000);
                    sleep(Duration::from_millis(200)).await;
                    awkernel_async_lib::r#yield().await;
                }
            },
            SchedulerType::EDF(1_000_000, CpuSet::empty().with(core)),
        )
        .await;
    }
}

/// Test 2: Verify a task with a multi-core CPU set only runs on cores
/// within the set.
async fn test_cluster_affinity() {
    if num_cpu() < 4 {
        log::info!("test_cluster_affinity: skipped (num_cpu < 4)");
        return;
    }
    log::info!("=== test_cluster_affinity start ===");

    // Cluster {1, 2}: the task must never run on other cores.
    let cluster = CpuSet::empty().with(1).with(2);
    spawn(
        "cluster_1_2".into(),
        async move {
            for _ in 0..5 {
                let actual = cpu_id();
                if cluster.contains(actual) {
                    log::info!("cluster_affinity: task ran on cpu {actual} [OK]");
                } else {
                    log::error!("cluster_affinity: task ran on cpu {actual} [FAIL]");
                }
                wait_microsec(100_000);
                sleep(Duration::from_millis(200)).await;
                awkernel_async_lib::r#yield().await;
            }
        },
        SchedulerType::EDF(1_000_000, cluster),
    )
    .await;
}

/// Test 3: Verify EDF preemption on a single core.
/// heavy (deadline=9900ms) is preempted by light (deadline=990ms) on core 1.
async fn test_edf_preemption() {
    log::info!("=== test_edf_preemption start ===");
    spawn_periodic_task("heavy".to_string(), 9_600_000, 10_000_000, 9_900_000, 1).await;
    spawn_periodic_task("light".to_string(), 900_000, 1_000_000, 990_000, 1).await;
}

/// Test 4: Verify core independence when num_cpu >= 3.
/// Tasks on core 1 and core 2 run in parallel without interfering.
async fn test_multi_core() {
    if num_cpu() < 3 {
        log::info!("test_multi_core: skipped (num_cpu < 3)");
        return;
    }
    log::info!("=== test_multi_core start ===");
    spawn_periodic_task("task_core1".to_string(), 4_000_000, 5_000_000, 4_900_000, 1).await;
    spawn_periodic_task("task_core2".to_string(), 4_000_000, 5_000_000, 4_900_000, 2).await;
}

/// Test 5: Verify the spawn-time fallback for invalid CPU sets.
/// An empty set, or a set naming only out-of-range cores, is normalized to
/// an empty worker set and falls back to all worker cores instead of being
/// rejected, so the task still runs — and never on CPU 0.
async fn test_empty_set_fallback() {
    log::info!("=== test_empty_set_fallback start ===");
    let workers = all_workers(num_cpu());

    // (a) an empty set, (b) a set whose only core is out of range.
    let invalid_sets = [CpuSet::empty(), CpuSet::empty().with(num_cpu())];
    for (i, set) in invalid_sets.into_iter().enumerate() {
        spawn(
            alloc::format!("fallback_{i}").into(),
            async move {
                for _ in 0..3 {
                    let actual = cpu_id();
                    if actual != 0 && workers.contains(actual) {
                        log::info!("empty_set_fallback: case {i} ran on worker cpu {actual} [OK]");
                    } else {
                        log::error!("empty_set_fallback: case {i} ran on cpu {actual} [FAIL]");
                    }
                    wait_microsec(100_000);
                    sleep(Duration::from_millis(200)).await;
                    awkernel_async_lib::r#yield().await;
                }
            },
            SchedulerType::EDF(1_000_000, set),
        )
        .await;
    }
}

/// Spawn a pseudo-periodic task pinned to `core`.
async fn spawn_periodic_task(
    task_name: String,
    exe_time: u64,
    period: u64,
    relative_deadline: u64,
    core: usize,
) {
    let task_name_clone = task_name.clone();
    spawn(
        task_name.into(),
        async move {
            loop {
                let start_time = uptime();
                wait_microsec(exe_time);
                let end_time = uptime();
                log::debug!(
                    "{}: cpu={}, start={}, end={}",
                    task_name_clone,
                    cpu_id(),
                    start_time,
                    end_time,
                );
                sleep(Duration::from_micros(period - exe_time)).await;
                awkernel_async_lib::r#yield().await;
            }
        },
        SchedulerType::EDF(relative_deadline, CpuSet::empty().with(core)),
    )
    .await;
}
