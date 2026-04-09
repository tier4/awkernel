#![no_std]

extern crate alloc;

use alloc::format;
use core::sync::atomic::{AtomicU32, Ordering};

use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::delay::wait_millisec;

const NUM_WORKERS: u32 = 32;
const EXPECTED_FIRST: u32 = 0;

static FIRST_STARTED: AtomicU32 = AtomicU32::new(u32::MAX);
static COMPLETED: AtomicU32 = AtomicU32::new(0);

/// This test confirms FIFO behavior for tasks with the same priority.
///
/// A high-priority controller enqueues same-priority workers while running,
/// so workers do not run until all are enqueued. Then we check the first
/// started worker ID.
pub async fn run() {
    wait_millisec(1000);
    FIRST_STARTED.store(u32::MAX, Ordering::SeqCst);
    COMPLETED.store(0, Ordering::SeqCst);

    spawn(
        "fifo_order_controller".into(),
        async move {
            for id in 0..NUM_WORKERS {
                spawn(
                    format!("fifo_worker_{id}").into(),
                    async move {
                        let _ = FIRST_STARTED.compare_exchange(
                            u32::MAX,
                            id,
                            Ordering::SeqCst,
                            Ordering::SeqCst,
                        );

                        let done = COMPLETED.fetch_add(1, Ordering::SeqCst) + 1;
                        if done == NUM_WORKERS {
                            let first = FIRST_STARTED.load(Ordering::SeqCst);
                            log::debug!(
                                "FIFO first_started={first}, expected={EXPECTED_FIRST}, workers={NUM_WORKERS}"
                            );
                            assert_eq!(first, EXPECTED_FIRST);
                        }
                    },
                    SchedulerType::PrioritizedFIFO(0),
                )
                .await;
            }
        },
        SchedulerType::PrioritizedFIFO(31),
    )
    .await;
}
