#![no_std]

extern crate alloc;

use alloc::vec;
use awkernel_async_lib::{
    dag::{create_dag, finish_create_dags},
    scheduler::SchedulerType,
    sleep,
};
use awkernel_lib::cpu::{cpu_id, num_cpu, CpuSet};
use core::{
    sync::atomic::{AtomicU8, Ordering},
    time::Duration,
};

// 0: warming up, 1: observing, 2: pass, 3: fail.
static PHASE: AtomicU8 = AtomicU8::new(0);
// 0: neither branch, 1: early branch, 2: early then late, 3: wrong order/CPU.
static ORDER: AtomicU8 = AtomicU8::new(0);

fn record_branch(expected: u8, next: u8) {
    if PHASE.load(Ordering::Acquire) != 1 {
        return;
    }

    if cpu_id() != 1
        || ORDER
            .compare_exchange(expected, next, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
    {
        ORDER.store(3, Ordering::Release);
    }
}

/// Exercise LLFT on one worker and report success only after the sink runs.
///
/// ```text
///                 +--> llft_late (10 ms) --------------------------+
/// source (1 ms) --+                                                +--> sink (10 ms)
///                 +--> llft_early (10 ms) --> llft_tail (200 ms) --+
/// ```
///
/// # Errors
///
/// Returns an error if the DAG cannot be created or completed, or the observed
/// branch order or CPU is wrong.
pub async fn run() {
    if num_cpu() < 2 {
        log::warn!("test_llft requires at least two CPUs");
        return;
    }

    let cpu = CpuSet::empty().with(1);
    let llft = SchedulerType::LLFT(1_000_000, cpu);
    let dag = create_dag();

    dag.register_periodic_reactor::<_, (u8, u8)>(
        "llft_source".into(),
        || (0, 0),
        vec!["llft_late_input".into(), "llft_early_input".into()],
        llft,
        Duration::from_secs(3),
        Some(Duration::from_millis(1)),
    )
    .await;

    dag.register_reactor::<_, (u8,), (u8,)>(
        "llft_late".into(),
        |(value,)| {
            record_branch(1, 2);
            (value,)
        },
        vec!["llft_late_input".into()],
        vec!["llft_late_output".into()],
        llft,
        Some(Duration::from_millis(10)),
    )
    .await;

    dag.register_reactor::<_, (u8,), (u8,)>(
        "llft_early".into(),
        |(value,)| {
            record_branch(0, 1);
            (value,)
        },
        vec!["llft_early_input".into()],
        vec!["llft_early_output".into()],
        llft,
        Some(Duration::from_millis(10)),
    )
    .await;

    dag.register_reactor::<_, (u8,), (u8,)>(
        "llft_tail".into(),
        |(value,)| (value,),
        vec!["llft_early_output".into()],
        vec!["llft_tail_output".into()],
        llft,
        Some(Duration::from_millis(200)),
    )
    .await;

    dag.register_sink_reactor::<_, (u8, u8)>(
        "llft_sink".into(),
        |(_, _)| match PHASE.load(Ordering::Acquire) {
            // The first complete job ensures both branches have received once
            // and returned to their waiting state before the observed release.
            0 => PHASE.store(1, Ordering::Release),
            1 => {
                let result = if cpu_id() == 1 && ORDER.load(Ordering::Acquire) == 2 {
                    2
                } else {
                    3
                };
                PHASE.store(result, Ordering::Release);
            }
            _ => {}
        },
        vec!["llft_late_output".into(), "llft_tail_output".into()],
        llft,
        Duration::from_secs(1),
        Some(Duration::from_millis(10)),
    )
    .await;

    if let Err(errors) = finish_create_dags(core::slice::from_ref(&dag)).await {
        log::error!("test_llft: DAGs creation failed:");
        for error in errors {
            log::error!("- {error}");
        }
        return;
    }

    // With a 1000ms deadline, 10ms sink and 200ms early tail,
    // latest finishes are 990ms (late) and 790ms (early).
    // Bounded wait is only a liveness timeout; the verdict comes from the
    // recorded branch order and the second sink invocation, not elapsed time.
    for _ in 0..100 {
        match PHASE.load(Ordering::Acquire) {
            2 => {
                log::info!("test_llft: early then late on CPU 1; DAG completed [OK]");
                return;
            }
            3 => {
                log::error!("test_llft: wrong branch order or CPU [FAIL]");
                return;
            }
            _ => {}
        }
        // This sleep is owned and awaited here; no caller can cancel it.
        sleep(Duration::from_millis(100)).await;
    }

    log::error!("test_llft: timed out waiting for DAG completion [FAIL]");
}
