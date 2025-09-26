#![no_std]

extern crate alloc;

use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::num_cpu, delay::wait_millisec};

pub async fn run() {
    wait_millisec(1000);
    for i in 1..num_cpu() {
        let sched_type = if i % 3 == 0 {
            SchedulerType::PrioritizedFIFO(0)
        } else if i % 3 == 1 {
            SchedulerType::PrioritizedRR(0)
        } else {
            SchedulerType::GEDF(1000)
        };

        spawn(
            "low_priority".into(),
            async move {
                log::debug!("low priority task {i} started. sched_type = {sched_type:?}");
                wait_millisec(1000);
                log::debug!("low priority task {i} finished. sched_type = {sched_type:?}");
            },
            sched_type,
        )
        .await;
    }

    for i in 1..num_cpu() {
        let sched_type = if i % 3 == 0 {
            SchedulerType::PrioritizedFIFO(1)
        } else if i % 3 == 1 {
            SchedulerType::PrioritizedRR(1)
        } else {
            SchedulerType::GEDF(500)
        };

        spawn(
            "high_priority".into(),
            async move {
                log::debug!("high priority task {i} started. sched_type = {sched_type:?}");
                wait_millisec(100);
                log::debug!("high priority task {i} finished. sched_type = {sched_type:?}");
            },
            sched_type,
        )
        .await;
    }
}
