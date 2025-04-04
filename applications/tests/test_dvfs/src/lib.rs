#![no_std]

use core::time::Duration;

extern crate alloc;

const APP_NAME: &str = "test DVFS";

const NUM_LOOP: usize = 100000000;

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
        let cpu_id = awkernel_lib::cpu::cpu_id();

        awkernel_lib::dvfs::set_max_performance(100);
        let elapsed1 = empty_loop();

        awkernel_lib::dvfs::set_max_performance(50);
        let elapsed2 = empty_loop();

        log::debug!(
            "cpu_id = {cpu_id:02}, first loop = {} [us], second loop = {} [us]",
            elapsed1.as_micros(),
            elapsed2.as_micros()
        );

        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    }
}

fn empty_loop() -> Duration {
    let t = awkernel_async_lib::time::Time::now();
    for _ in 0..NUM_LOOP {
        core::hint::black_box(());
    }
    t.elapsed()
}
