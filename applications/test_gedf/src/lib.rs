#![no_std]

extern crate alloc;
use alloc::string::String;
use alloc::string::ToString;

use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::cpu_id, delay::wait_microsec};

/// TODO: Test verification will be done after preemption implementation
/// Currently, only the order in which tasks are started is checked.
pub async fn run() {
    wait_microsec(1000000);

    // Generate tasks with pseudo-periods.
    // Assumption that periodic reactors are running.
    spawn_periodic_loop("periodic_loop_1".to_string(), 500000, 1000000, 800000).await;
    spawn_periodic_loop("periodic_loop_2".to_string(), 500000, 2000000, 600000).await;
    spawn_periodic_loop("periodic_loop_3".to_string(), 500000, 3000000, 2800000).await;
}

/// Spawn a pseudo-periodic task.
async fn spawn_periodic_loop(
    task_name: String,
    exe_time: u64,
    period: u64,
    relative_deadline: u64,
) {
    let task_name_clone = task_name.clone();
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
