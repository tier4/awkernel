#![no_std]

extern crate alloc;
use alloc::string::String;
use alloc::string::ToString;

use awkernel_async_lib::sleep;
use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{
    cpu::{cpu_id, num_cpu},
    delay::{uptime, wait_microsec},
};
use core::time::Duration;

pub async fn run() {
    wait_microsec(2_000_000);

    if num_cpu() < 2 {
        log::warn!("test_partitioned_edf: requires at least 2 CPUs, skipping");
        return;
    }

    test_core_pinning().await;
    test_edf_preemption().await;
    test_multi_core().await;

    wait_microsec(100_000_000);
}

/// Test 1: Verify tasks are pinned to their assigned cores.
/// Spawns one periodic task per worker core (1..num_cpu()).
/// Each task checks cpu_id() matches the assigned core.
async fn test_core_pinning() {
    log::info!("=== test_core_pinning start ===");
    for core in 1..num_cpu() {
        let core_u16 = core as u16;
        spawn(
            alloc::format!("pinning_core{core}").into(),
            async move {
                for _ in 0..3 {
                    let actual = cpu_id();
                    if actual == core {
                        log::info!(
                            "core_pinning: task on core {core} ran on cpu {actual} [OK]"
                        );
                    } else {
                        log::error!(
                            "core_pinning: task on core {core} ran on cpu {actual} [FAIL]"
                        );
                    }
                    wait_microsec(100_000);
                    sleep(Duration::from_millis(200)).await;
                    awkernel_async_lib::r#yield().await;
                }
            },
            SchedulerType::PartitionedEDF(1_000_000, core_u16),
        )
        .await;
    }
}

/// Test 2: Verify EDF preemption on a single core.
/// heavy (deadline=9900ms) is preempted by light (deadline=990ms) on core 1.
async fn test_edf_preemption() {
    log::info!("=== test_edf_preemption start ===");
    spawn_periodic_task("heavy".to_string(), 9_600_000, 10_000_000, 9_900_000, 1).await;
    spawn_periodic_task("light".to_string(), 900_000, 1_000_000, 990_000, 1).await;
}

/// Test 3: Verify core independence when num_cpu >= 3.
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

/// Spawn a pseudo-periodic task pinned to `core`.
async fn spawn_periodic_task(
    task_name: String,
    exe_time: u64,
    period: u64,
    relative_deadline: u64,
    core: u16,
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
        SchedulerType::PartitionedEDF(relative_deadline, core),
    )
    .await;
}
