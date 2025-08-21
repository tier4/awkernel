#![no_std]

extern crate alloc;

use alloc::format;

use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::num_cpu, delay::wait_millisec};

/// This test confirms whether PrioritizedFIFO scheduler actually schedules
/// high priority tasks prior to low priority tasks.
pub async fn run() {
    wait_millisec(1000);

    for i in 1..num_cpu() {
        spawn(
            format!("low_priority {i}").into(),
            async move {
                log::debug!("low priority {i} task started.");
                wait_millisec(100);
                spawn(
                    format!("high_priority {i}").into(),
                    async move {
                        log::debug!("high priority {i} task started.");
                        wait_millisec(100);
                        log::debug!("high priority {i} task finished.");
                    },
                    SchedulerType::PrioritizedFIFO(31),
                )
                .await;
                wait_millisec(100);
                log::debug!("low priority {i} task finished.");
            },
            SchedulerType::PrioritizedFIFO(0),
        )
        .await;
    }
}
