#![no_std]

extern crate alloc;

use awkernel_async_lib::task::get_preemptable_tasks;
use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::delay::uptime;
use awkernel_lib::{cpu::cpu_id, delay::wait_microsec};

#[allow(dead_code)]
enum TestType {
    GetPreemptableTasks,
    GetPreemptableTasksLess,
    SchedPreempt,
    TaskPreempt,
}

pub async fn run() {
    wait_microsec(100000);

    let test_type = TestType::SchedPreempt;
    match test_type {
        TestType::GetPreemptableTasks => check_get_preemptable_normal().await,
        TestType::GetPreemptableTasksLess => check_get_preemptable_less().await,
        TestType::SchedPreempt => check_sched_preempt().await,
        TestType::TaskPreempt => check_task_preempt().await,
    }
}

async fn check_get_preemptable_normal() {
    log::info!("[{}] GEDF spawn", uptime());
    spawn(
        "GEDF".into(),
        async move {
            log::info!("[{}] GEDF is start at cpu_id: {}", uptime(), cpu_id());
            wait_microsec(10000000);
            log::info!("[{}] GEDF is end at cpu_id: {}", uptime(), cpu_id());
        },
        SchedulerType::GEDF(99000000),
    )
    .await;
    log::info!("[{}] RR spawn", uptime());
    spawn(
        "RR".into(),
        async move {
            log::info!("[{}] RR is start at cpu_id: {}", uptime(), cpu_id());
            wait_microsec(10000000);
            log::info!("[{}] RR is end at cpu_id: {}", uptime(), cpu_id());
        },
        SchedulerType::RR,
    )
    .await;

    wait_microsec(100000);
    let preemptable_tasks = match get_preemptable_tasks() {
        Some(preemptable_tasks) => preemptable_tasks,
        None => return,
    };
    log::info!("[{}] preemptable_tasks: {:?}", uptime(), preemptable_tasks);
}

async fn check_get_preemptable_less() {
    let _preemptable_tasks = match get_preemptable_tasks() {
        Some(preemptable_tasks) => preemptable_tasks,
        None => {
            log::info!("get_preemptable_tasks() is None");
            return;
        }
    };
}

async fn check_sched_preempt() {
    log::info!(
        "[{}] test_sched_preempt is start at cpu_id: {}",
        uptime(),
        cpu_id()
    );
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

    log::info!(
        "[{}] test_sched_preempt is end at cpu_id: {}",
        uptime(),
        cpu_id()
    );
}

async fn check_task_preempt() {
    log::info!(
        "[{}] test_sched_preempt is start at cpu_id: {}",
        uptime(),
        cpu_id()
    );
    log::info!("[{}] GEDF_L1 spawn", uptime());
    spawn(
        "GEDF_L1".into(),
        async move {
            log::info!("[{}] GEDF_L1 is start at cpu_id: {}", uptime(), cpu_id());
            wait_microsec(200000);
            log::info!("[{}] GEDF_L1 is end at cpu_id: {}", uptime(), cpu_id());
        },
        SchedulerType::GEDF(1000000),
    )
    .await;
    log::info!("[{}] GEDF_M1 spawn", uptime());
    spawn(
        "GEDF_M1".into(),
        async move {
            log::info!("[{}] GEDF_M1 is start at cpu_id: {}", uptime(), cpu_id());
            wait_microsec(200000);
            log::info!("[{}] GEDF_M1 is end at cpu_id: {}", uptime(), cpu_id());
        },
        SchedulerType::GEDF(90000),
    )
    .await;
    log::info!("[{}] GEDF_H1 spawn", uptime());
    spawn(
        "GEDF_H1".into(),
        async move {
            log::info!("[{}] GEDF_H1 is start at cpu_id: {}", uptime(), cpu_id());
            wait_microsec(10000);
            log::info!("[{}] GEDF_H1 is end at cpu_id: {}", uptime(), cpu_id());
        },
        SchedulerType::GEDF(80000),
    )
    .await;

    wait_microsec(100000);
    log::info!(
        "[{}] test_sched_preempt is end at cpu_id: {}",
        uptime(),
        cpu_id()
    );
}
