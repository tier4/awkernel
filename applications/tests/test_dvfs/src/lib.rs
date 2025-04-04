#![no_std]

use core::time::Duration;

extern crate alloc;

const APP_NAME: &str = "test DVFS";

const NUM_LOOP: usize = 1000000;

pub async fn run() {
    awkernel_async_lib::spawn(
        APP_NAME.into(),
        test_dvfs(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn test_dvfs() {
    loop {
        // TODO: update CPU freq
        let t = awkernel_async_lib::time::Time::now();

        for _ in 0..NUM_LOOP {
            core::hint::black_box(());
        }

        let elapsed1 = t.elapsed();

        // TODO: update CPU freq

        let t = awkernel_async_lib::time::Time::now();

        for _ in 0..NUM_LOOP {
            core::hint::black_box(());
        }
        let elapsed2 = t.elapsed();

        log::debug!(
            "first loop = {} [us], second loop = {} [us]",
            elapsed1.as_micros(),
            elapsed2.as_micros()
        );

        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    }
}
