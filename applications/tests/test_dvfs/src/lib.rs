#![no_std]

use core::time::Duration;

extern crate alloc;

const APP_NAME: &str = "test DVFS";

const NUM_LOOP: usize = 1000000;

pub async fn run() {
    awkernel_async_lib::spawn(
        APP_NAME.into(),
        test_dvfs(),
        awkernel_async_lib::scheduler::SchedulerType::PrioritizedFIFO(31),
    )
    .await;
}

async fn test_dvfs() {
    loop {
        let max = awkernel_lib::dvfs::get_max_freq();
        let cpuid = awkernel_lib::cpu::cpu_id();

        // Maximum frequency.
        awkernel_lib::dvfs::fix_freq(max);

        let start = awkernel_async_lib::time::Time::now();

        for _ in 0..NUM_LOOP {
            core::hint::black_box(());
        }

        let t = start.elapsed();

        let current = awkernel_lib::dvfs::get_curr_freq();

        log::debug!(
            "cpuid = {cpuid}, max = {max}, current = {current}, expected = {max}, time = {t:?}"
        );

        // Maximum / 2 frequency.
        awkernel_lib::dvfs::fix_freq(max / 2);

        let start = awkernel_async_lib::time::Time::now();

        for _ in 0..NUM_LOOP {
            core::hint::black_box(());
        }

        let t = start.elapsed();

        let current = awkernel_lib::dvfs::get_curr_freq();

        log::debug!(
            "cpuid = {cpuid}, max = {max}, current = {current}, expected = {}, time = {t:?}",
            max / 2
        );

        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    }
}
