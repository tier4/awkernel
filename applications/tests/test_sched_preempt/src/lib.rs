#![no_std]

use awkernel_async_lib::{scheduler::SchedulerType, spawn, task::get_lowest_priority_task_info};
use awkernel_lib::{
    cpu::cpu_id,
    delay::{uptime, wait_microsec},
};

#[allow(dead_code)]
enum TestType {
    GetlowestTask,
    SchedPreempt,
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

    let test_type = TestType::SchedPreempt;
    match test_type {
        TestType::GetlowestTask => check_lowest_task().await,
        TestType::SchedPreempt => check_sched_preempt().await,
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

async fn check_sched_preempt() {
    log::info!("[{}] GEDF_H1 spawn", uptime());
    spawn(
        "GEDF_H1".into(),
        async move {
            log::info!("[{}] GEDF_H1 is start at cpu_id: {}", uptime(), cpu_id());
            wait_microsec(10000000);
            log::info!("[{}] GEDF_H1 is end at cpu_id: {}", uptime(), cpu_id());
        },
        SchedulerType::GEDF(99000000),
    )
    .await;
    log::info!("[{}] FIFO_L1 spawn", uptime());
    spawn(
        "FIFO_M1".into(),
        async move {
            log::info!("[{}] FIFO_M1 is start at cpu_id: {}", uptime(), cpu_id());
            wait_microsec(10000000);
            log::info!("[{}] FIFO_M1 is end at cpu_id: {}", uptime(), cpu_id());
        },
        SchedulerType::FIFO,
    )
    .await;
    log::info!("[{}] RR_L1 spawn", uptime());
    spawn(
        "RR_L1".into(),
        async move {
            log::info!("[{}] RR_L1 is start at cpu_id: {}", uptime(), cpu_id());
            wait_microsec(10000000);
            log::info!("[{}] RR_L1 is end at cpu_id: {}", uptime(), cpu_id());
        },
        SchedulerType::RR,
    )
    .await;
    log::info!("[{}] GEDF_H2 spawn", uptime());
    spawn(
        "GEDF_H2".into(),
        async move {
            log::info!("[{}] GEDF_H2 is start at cpu_id: {}", uptime(), cpu_id());
            wait_microsec(10000000);
            log::info!("[{}] GEDF_H2 is end at cpu_id: {}", uptime(), cpu_id());
        },
        SchedulerType::GEDF(98000000),
    )
    .await;
}