#![no_std]

use awkernel_async_lib::{scheduler::SchedulerType, spawn, task::get_lowest_priority_task_info};
use awkernel_lib::{
    cpu::cpu_id,
    delay::{uptime, wait_microsec},
};

#[allow(dead_code)]
enum TestType {
    GetlowestTask,
}

/// Tests related to preemption between schedulers
pub async fn run() {
    // TASK ID:1
    wait_microsec(100000);
    log::info!(
        "[{}] Start test_sched_preempt at cpu_id: {}",
        uptime(),
        cpu_id()
    );

    let test_type = TestType::GetlowestTask;
    match test_type {
        TestType::GetlowestTask => check_lowest_task().await,
    }

    log::info!(
        "[{}] End test_sched_preempt at cpu_id: {}",
        uptime(),
        cpu_id()
    );
}

async fn check_lowest_task() {
    spawn(
        // TASK ID:8
        "GEDF".into(),
        async move {
            loop {
                log::info!("[{}] GEDF is start at cpu_id: {}", uptime(), cpu_id());
                wait_microsec(10000000);
                log::info!("[{}] GEDF is end at cpu_id: {}", uptime(), cpu_id());
            }
        },
        SchedulerType::GEDF(10000),
    )
    .await;
    spawn(
        // TASK ID:9
        "FIFO".into(),
        async move {
            loop {
                log::info!("[{}] FIFO is start at cpu_id: {}", uptime(), cpu_id());
                wait_microsec(10000000);
                log::info!("[{}] FIFO is end at cpu_id: {}", uptime(), cpu_id());
            }
        },
        SchedulerType::FIFO,
    )
    .await;

    wait_microsec(1000000);

    // FIFO TASK ID:1 < FIFO TASK ID:9 < GEDF TASK ID:8
    // In FIFO tasks, the task with the smaller CPU ID has the lowest priority.
    if let Some((task_id, cpu_id, _)) = get_lowest_priority_task_info() {
        log::debug!("Task ID: {}, cpu_id: {}", task_id, cpu_id,);
    }
}
