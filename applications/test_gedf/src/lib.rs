#![no_std]

use awkernel_async_lib::scheduler::gedf;
use awkernel_async_lib::task::get_current_task;
use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::cpu_id, delay::wait_microsec};

/// This test verifies that the GEDF scheduler adheres to the startup order and startup timing.
pub async fn run() {
    wait_microsec(1000000);

    spawn(
        "infinite_loop_1".into(),
        async move {
            gedf::SCHEDULER.register_task(get_current_task(cpu_id()).unwrap());
            loop {
                log::debug!(
                    "infinite loop 1 task, task_id={}, cpu_id={}",
                    get_current_task(cpu_id()).unwrap(),
                    cpu_id()
                );
                wait_microsec(500000);
                gedf::SCHEDULER.increment_ignition(get_current_task(cpu_id()).unwrap());
                awkernel_async_lib::r#yield().await;
            }
        },
        SchedulerType::GEDF(1000000, 600000, awkernel_lib::delay::uptime()),
    )
    .await;

    spawn(
        "infinite_loop_2".into(),
        async move {
            gedf::SCHEDULER.register_task(get_current_task(cpu_id()).unwrap());
            loop {
                log::debug!(
                    "infinite loop 2 task, task_id={}, cpu_id={}",
                    get_current_task(cpu_id()).unwrap(),
                    cpu_id()
                );
                wait_microsec(400000);
                gedf::SCHEDULER.increment_ignition(get_current_task(cpu_id()).unwrap());
                awkernel_async_lib::r#yield().await;
            }
        },
        SchedulerType::GEDF(1500000, 500000, awkernel_lib::delay::uptime()),
    )
    .await;

    spawn(
        "infinite_loop_3".into(),
        async move {
            gedf::SCHEDULER.register_task(get_current_task(cpu_id()).unwrap());
            loop {
                log::debug!(
                    "infinite loop 3 task, task_id={}, cpu_id={}",
                    get_current_task(cpu_id()).unwrap(),
                    cpu_id()
                );
                wait_microsec(300000);
                gedf::SCHEDULER.increment_ignition(get_current_task(cpu_id()).unwrap());
                awkernel_async_lib::r#yield().await;
            }
        },
        SchedulerType::GEDF(2000000, 400000, awkernel_lib::delay::uptime()),
    )
    .await;

    spawn(
        "infinite_loop_4".into(),
        async move {
            gedf::SCHEDULER.register_task(get_current_task(cpu_id()).unwrap());
            loop {
                log::debug!(
                    "infinite loop 4 task, task_id={}, cpu_id={}",
                    get_current_task(cpu_id()).unwrap(),
                    cpu_id()
                );
                wait_microsec(700000);
                gedf::SCHEDULER.increment_ignition(get_current_task(cpu_id()).unwrap());
                awkernel_async_lib::r#yield().await;
            }
        },
        SchedulerType::GEDF(3000000, 800000, awkernel_lib::delay::uptime()),
    )
    .await;

    spawn(
        "infinite_loop_5".into(),
        async move {
            gedf::SCHEDULER.register_task(get_current_task(cpu_id()).unwrap());
            loop {
                log::debug!(
                    "infinite loop 5 task, task_id={}, cpu_id={}",
                    get_current_task(cpu_id()).unwrap(),
                    cpu_id()
                );
                wait_microsec(600000);
                gedf::SCHEDULER.increment_ignition(get_current_task(cpu_id()).unwrap());
                awkernel_async_lib::r#yield().await;
            }
        },
        SchedulerType::GEDF(1000000, 800000, awkernel_lib::delay::uptime()),
    )
    .await;
}
