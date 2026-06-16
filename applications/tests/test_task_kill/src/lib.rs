#![no_std]

extern crate alloc;

use awkernel_async_lib::{scheduler::SchedulerType, sleep, task};
use core::time::Duration;

pub async fn run() {
    sleep(Duration::from_secs(1)).await;
    log::info!("TASK_KILL_TEST start");

    kill_sleeping_task().await;
    kill_unknown_id();
    kill_idempotent().await;

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
