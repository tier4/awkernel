#![no_std]

use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::num_cpu, delay::wait_millisec};

/// This test confirms whether PriorityBasedRR scheduler works
/// both as a priority based scheduler and as an RR scheduler
pub async fn run() {
    wait_millisec(1000);
    log::debug!("test_priority_based_rr");

    for i in 0..num_cpu() * 3 {
        spawn(
            "infinite_loop".into(),
            async move {
                loop {
                    let priority = i % 2;
                    log::debug!("infinite loop task, no={i}, priority={priority}");
                    wait_millisec(100);
                }
            },
            SchedulerType::PriorityBasedRR((i % 2) as u8),
        )
        .await;
    }
}
