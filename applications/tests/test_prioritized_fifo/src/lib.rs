#![no_std]

use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::num_cpu, delay::wait_millisec};

/// This test confirms whether PrioritizedFIFO scheduler actually schedules
/// high priority tasks prior to low priority tasks.
pub async fn run() {
    wait_millisec(1000);

    for i in 1..num_cpu() {
        spawn(
            "sleep".into(),
            async move {
                log::debug!("sleeping, core={i}");
                wait_millisec(1000);
            },
            SchedulerType::PrioritizedFIFO(0),
        )
        .await;
    }

    wait_millisec(500);

    for i in 1..num_cpu() {
        spawn(
            "low_priority".into(),
            async move {
                log::debug!("low priority task, core={i}");
                wait_millisec(100);
            },
            SchedulerType::PrioritizedFIFO(255),
        )
        .await;
    }

    for i in 1..num_cpu() {
        spawn(
            "high_priority".into(),
            async move {
                log::debug!("high priority task, core={i}");
                wait_millisec(100);
            },
            SchedulerType::PrioritizedFIFO(0),
        )
        .await;
    }
}
