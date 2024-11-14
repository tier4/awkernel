#![no_std]

extern crate alloc;
use alloc::string::String;
use alloc::string::ToString;

use awkernel_async_lib::scheduler::gedf;
use awkernel_async_lib::task::get_current_task;
use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::cpu_id, delay::wait_microsec};

/// This test verifies that the GEDF scheduler adheres to the startup order and startup timing.
pub async fn run() {
    wait_microsec(1000000);

    // task exe 0.5s, period 1s, deadline 0.8s
    spawn_infinite_loop("infinite_loop_1".to_string(), 500000, 1000000, 800000).await;
    // task exe 0.5s, period 2s, deadline 0.6s
    spawn_infinite_loop("infinite_loop_2".to_string(), 500000, 2000000, 600000).await;
    // task exe 0.5s, period 3s, deadline 2.8s
    spawn_infinite_loop("infinite_loop_3".to_string(), 500000, 3000000, 2800000).await;
}

/// Helper function to spawn an infinite loop task with specific parameters.
async fn spawn_infinite_loop(task_name: String, wait_duration: u64, period: u64, deadline: u64) {
    let task_name_clone = task_name.clone(); // Clone `task_name` to avoid moving into async block
    spawn(
        task_name.into(),
        async move {
            gedf::SCHEDULER.register_task(get_current_task(cpu_id()).unwrap());
            loop {
                let start_time = awkernel_lib::delay::uptime();
                wait_microsec(wait_duration);
                let end_time = awkernel_lib::delay::uptime();
                log::debug!(
                    "task_name: {}, cpu_id: {}, start_time: {}, end_time: {}",
                    task_name_clone,
                    cpu_id(),
                    start_time,
                    end_time
                );
                gedf::SCHEDULER.increment_ignition(get_current_task(cpu_id()).unwrap());
                awkernel_async_lib::r#yield().await;
            }
        },
        SchedulerType::GEDF(period, deadline, awkernel_lib::delay::uptime()),
    )
    .await;
}
