#![no_std]

extern crate alloc;
use alloc::string::String;
use alloc::string::ToString;

use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::cpu_id, delay::wait_microsec};

/// This test verifies that the GEDF scheduler adheres to the startup order and startup timing.
pub async fn run() {
    wait_microsec(1000000);

    // exe_time 0.5s, period 1s, relative_deadline 0.8s
    spawn_infinite_loop("infinite_loop_1".to_string(), 500000, 1000000, 800000).await;
    // exe_time 0.5s, period 2s, relative_deadline 0.6s
    spawn_infinite_loop("infinite_loop_2".to_string(), 500000, 2000000, 600000).await;
    // exe_time 0.5s, period 3s, relative_deadline 2.8s
    spawn_infinite_loop("infinite_loop_3".to_string(), 500000, 3000000, 2800000).await;
}

/// Helper function to spawn an infinite loop task with specific parameters.
async fn spawn_infinite_loop(task_name: String, exe_time: u64, period: u64, relative_deadline: u64) {
    let task_name_clone = task_name.clone(); // Clone `task_name` to avoid moving into async block
    spawn(
        task_name.into(),
        async move {
            loop {
                let start_time = awkernel_lib::delay::uptime();
                wait_microsec(exe_time);
                let end_time = awkernel_lib::delay::uptime();
                log::debug!(
                    "task_name: {}, cpu_id: {}, start_time: {}, end_time: {}",
                    task_name_clone,
                    cpu_id(),
                    start_time,
                    end_time
                );
                wait_microsec(period - exe_time);
                awkernel_async_lib::r#yield().await;
            }
        },
        SchedulerType::GEDF(relative_deadline),
    )
    .await;
}
