#![no_std]

extern crate alloc;

use awkernel_async_lib::{scheduler::SchedulerType, sleep, task};
use core::{
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

struct DropTracker;

impl Drop for DropTracker {
    fn drop(&mut self) {
        DROP_COUNT.fetch_add(1, Ordering::Release);
    }
}

pub async fn run() {
    sleep(Duration::from_secs(1)).await;
    log::info!("TASK_KILL_TEST start");

    kill_sleeping_task().await;
    kill_unknown_id();
    kill_idempotent().await;
    resources_freed_after_kill().await;

    log::info!("TASK_KILL_TEST done");
}

async fn kill_sleeping_task() {
    let id = task::spawn(
        "kill-target".into(),
        async {
            loop {
                sleep(Duration::from_secs(3600)).await;
            }
        },
        SchedulerType::PrioritizedFIFO(0),
    );

    sleep(Duration::from_millis(50)).await;

    if task::kill(id) {
        log::info!("TASK_KILL_TEST kill_sleeping_task: PASS (kill returned true)");
    } else {
        log::error!("TASK_KILL_TEST kill_sleeping_task: FAIL (kill returned false)");
    }

    sleep(Duration::from_millis(50)).await;

    if task::get_task(id).is_none() {
        log::info!("TASK_KILL_TEST task_removed_from_registry: PASS");
    } else {
        log::error!("TASK_KILL_TEST task_removed_from_registry: FAIL (still in registry)");
    }
}

fn kill_unknown_id() {
    if !task::kill(u32::MAX) {
        log::info!("TASK_KILL_TEST kill_unknown_id: PASS");
    } else {
        log::error!("TASK_KILL_TEST kill_unknown_id: FAIL (returned true for unknown id)");
    }
}

async fn kill_idempotent() {
    let id = task::spawn(
        "kill-twice".into(),
        async {
            loop {
                sleep(Duration::from_secs(3600)).await;
            }
        },
        SchedulerType::PrioritizedFIFO(0),
    );

    sleep(Duration::from_millis(50)).await;
    task::kill(id);

    if !task::kill(id) {
        log::info!("TASK_KILL_TEST kill_idempotent: PASS (second kill returned false)");
    } else {
        log::error!("TASK_KILL_TEST kill_idempotent: FAIL (second kill returned true)");
    }
}

async fn resources_freed_after_kill() {
    DROP_COUNT.store(0, Ordering::Release);

    // The task owns a DropTracker and sleeps 200 ms per iteration.
    // sleep() stores the Waker in a timer closure, which holds the last Arc<Task>
    // reference after kill() removes the task from TASKS.  When the timer fires
    // the closure drops the Waker → Arc<Task> → 0 → Future → DropTracker::drop().
    let id = task::spawn(
        "drop-tracker-task".into(),
        async {
            let _tracker = DropTracker;
            loop {
                sleep(Duration::from_millis(200)).await;
            }
        },
        SchedulerType::PrioritizedFIFO(0),
    );

    // Let the task enter its first 200 ms sleep (Waiting state).
    sleep(Duration::from_millis(50)).await;

    task::kill(id);

    // Wait for the timer to fire (~150 ms remaining) plus a safety margin.
    sleep(Duration::from_millis(300)).await;

    if DROP_COUNT.load(Ordering::Acquire) == 1 {
        log::info!("TASK_KILL_TEST resources_freed_after_kill: PASS");
    } else {
        log::error!(
            "TASK_KILL_TEST resources_freed_after_kill: FAIL (drop_count={})",
            DROP_COUNT.load(Ordering::Acquire)
        );
    }
}
