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
    kill_preempted_task().await;
    kill_panicked_task().await;

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

async fn kill_preempted_task() {
    log::info!("TASK_KILL_TEST kill_preempted_task: step 1 start");
    DROP_COUNT.store(0, Ordering::Release);

    // Spin-loop followed by a short sleep: the spin phase is interrupted by the timer
    // preemption interrupt, putting the task in State::Preempted.  PrioritizedRR enables
    // time-slicing preemption; PrioritizedFIFO does not.  The sleep gives the deferred
    // kill_pending machinery an await point to trigger on.
    let id = task::spawn(
        "preempt-target".into(),
        async {
            let _tracker = DropTracker;
            loop {
                for _ in 0..500_000u64 {
                    core::hint::spin_loop();
                }
                sleep(Duration::from_millis(10)).await;
            }
        },
        SchedulerType::PrioritizedRR(0),
    );

    log::info!("TASK_KILL_TEST kill_preempted_task: step 2 spawned id={}", id);

    // Allow the task to run and be preempted at least once.
    sleep(Duration::from_millis(50)).await;

    log::info!("TASK_KILL_TEST kill_preempted_task: step 3 after sleep 50ms");

    // kill() may find the task in Preempted, Running, or Waiting state.
    let killed = task::kill(id);

    log::info!("TASK_KILL_TEST kill_preempted_task: step 4 kill={}", killed);

    if !killed {
        log::error!("TASK_KILL_TEST kill_preempted_task: FAIL (kill returned false)");
        return;
    }

    // If the task was Preempted when killed, it resumes via yield_and_pool and terminates
    // at the next await (sleep 10 ms).  Allow enough margin for that path.
    sleep(Duration::from_millis(300)).await;

    log::info!("TASK_KILL_TEST kill_preempted_task: step 5 after sleep 300ms");

    if task::get_task(id).is_some() {
        log::error!("TASK_KILL_TEST kill_preempted_task: FAIL (task still in registry)");
        return;
    }

    if DROP_COUNT.load(Ordering::Acquire) == 1 {
        log::info!("TASK_KILL_TEST kill_preempted_task: PASS");
    } else {
        log::error!(
            "TASK_KILL_TEST kill_preempted_task: FAIL (drop_count={})",
            DROP_COUNT.load(Ordering::Acquire)
        );
    }
}

async fn kill_panicked_task() {
    log::info!("TASK_KILL_TEST kill_panicked_task: step 1 start");

    let id = task::spawn(
        "panicked-target".into(),
        async {
            panic!("intentional panic for kill semantics test");
        },
        SchedulerType::PrioritizedFIFO(0),
    );

    // Let the task start and transition to Panicked after panic handling.
    sleep(Duration::from_millis(100)).await;

    if task::get_task(id).is_none() {
        log::info!("TASK_KILL_TEST kill_panicked_task: PASS (panicked task removed from registry)");
    } else {
        log::error!("TASK_KILL_TEST kill_panicked_task: FAIL (panicked task still in registry)");
    }

    // Panicked tasks are terminal; kill() should return false and not mutate state.
    if !task::kill(id) {
        log::info!("TASK_KILL_TEST kill_panicked_task: PASS (kill returned false)");
    } else {
        log::error!("TASK_KILL_TEST kill_panicked_task: FAIL (kill returned true)");
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
