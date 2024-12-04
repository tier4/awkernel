#![no_std]

extern crate alloc;
use awkernel_async_lib::{scheduler::SchedulerType, spawn};
use awkernel_lib::{cpu::cpu_id, delay::wait_microsec};

pub async fn run() {
    wait_microsec(1000000);

    log::debug!(
        "[{}] test_sched_preempt is start at cpu_id: {}",
        awkernel_lib::delay::uptime(),
        cpu_id()
    );

    log::debug!("[{}] GEDF_H1 spawn", awkernel_lib::delay::uptime());
    spawn(
        "GEDF_H1".into(),
        async move {
            log::debug!(
                "[{}] GEDF_H1 is start at cpu_id: {}",
                awkernel_lib::delay::uptime(),
                cpu_id()
            );
            wait_microsec(10000000);
            log::debug!(
                "[{}] GEDF_H1 is end at cpu_id: {}",
                awkernel_lib::delay::uptime(),
                cpu_id()
            );
        },
        SchedulerType::GEDF(10000000),
    )
    .await;

    log::debug!("[{}] FIFO_M1 spawn", awkernel_lib::delay::uptime());
    spawn(
        "FIFO_M1".into(),
        async move {
            log::debug!(
                "[{}] FIFO_M1 is start at cpu_id: {}",
                awkernel_lib::delay::uptime(),
                cpu_id()
            );
            wait_microsec(10000000);
            log::debug!(
                "[{}] FIFO_M1 is end at cpu_id: {}",
                awkernel_lib::delay::uptime(),
                cpu_id()
            );
        },
        SchedulerType::FIFO,
    )
    .await;

    log::debug!("[{}] RR_L1 spawn", awkernel_lib::delay::uptime());
    spawn(
        "RR_L1".into(),
        async move {
            log::debug!(
                "[{}] RR_L1 is start at cpu_id: {}",
                awkernel_lib::delay::uptime(),
                cpu_id()
            );
            wait_microsec(10000000);
            log::debug!(
                "[{}] RR_L1 is end at cpu_id: {}",
                awkernel_lib::delay::uptime(),
                cpu_id()
            );
        },
        SchedulerType::RR,
    )
    .await;

    log::debug!("[{}] GEDF_H2 spawn", awkernel_lib::delay::uptime());
    spawn(
        "GEDF_H2".into(),
        async move {
            log::debug!(
                "[{}] GEDF_H2 is start at cpu_id: {}",
                awkernel_lib::delay::uptime(),
                cpu_id()
            );
            wait_microsec(10000000);
            log::debug!(
                "[{}] GEDF_H2 is end at cpu_id: {}",
                awkernel_lib::delay::uptime(),
                cpu_id()
            );
        },
        SchedulerType::GEDF(9000000),
    )
    .await;

    wait_microsec(10000);

    log::debug!(
        "[{}] test_sched_preempt is end at cpu_id: {}",
        awkernel_lib::delay::uptime(),
        cpu_id()
    );
}
