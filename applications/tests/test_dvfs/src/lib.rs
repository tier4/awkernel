#![no_std]

use core::time::Duration;

extern crate alloc;

const APP_NAME: &str = "test DVFS";

const NUM_LOOP: usize = 1000000;

pub async fn run() {
    awkernel_async_lib::spawn(
        APP_NAME.into(),
        test_dvfs(),
        awkernel_async_lib::scheduler::SchedulerType::PrioritizedFIFO(0),
    )
    .await;
}

async fn test_dvfs() {
    loop {
        let cpuid = awkernel_lib::cpu::cpu_id();
        let max = match awkernel_lib::dvfs::get_max_cpu_freq() {
            Ok(freq) => freq,
            Err(e) => {
                log::error!("Failed to get max CPU frequency: {:?}", e);
                return;
            }
        };

        // Maximum frequency.
        if let Err(e) = awkernel_lib::dvfs::set_cpu_freq(max) {
            log::error!("Failed to set CPU frequency: {:?}", e);
            return;
        }

        let start = awkernel_async_lib::time::Time::now();

        for _ in 0..NUM_LOOP {
            core::hint::black_box(());
        }

        let t = start.elapsed();

        let current = match awkernel_lib::dvfs::get_curr_cpu_freq() {
            Ok(freq) => freq,
            Err(e) => {
                log::error!("Failed to get current CPU frequency: {:?}", e);
                return;
            }
        };

        log::debug!(
            "cpuid = {cpuid}, max = {max}, current = {current}, expected = {max}, time = {t:?}"
        );

        // Maximum / 2 frequency.
        if let Err(e) = awkernel_lib::dvfs::set_cpu_freq(max / 2) {
            log::error!("Failed to set CPU frequency: {:?}", e);
            return;
        }

        let start = awkernel_async_lib::time::Time::now();

        for _ in 0..NUM_LOOP {
            core::hint::black_box(());
        }

        let t = start.elapsed();

        let current = match awkernel_lib::dvfs::get_curr_cpu_freq() {
            Ok(freq) => freq,
            Err(e) => {
                log::error!("Failed to get current CPU frequency: {:?}", e);
                return;
            }
        };

        log::debug!(
            "cpuid = {cpuid}, max = {max}, current = {current}, expected = {}, time = {t:?}",
            max / 2
        );

        awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    }
}
