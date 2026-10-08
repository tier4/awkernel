#![no_std]

use awkernel_lib::{
    dvfs::{
        Result, get_curr_cpu_freq, get_max_cpu_freq, get_min_cpu_freq, set_cpu_freq,
        set_global_freq,
    },
    time::Time,
};
use core::time::Duration;

extern crate alloc;

const APP_NAME: &str = "test DVFS";

const NUM_LOOP: usize = 1000000;
const SEMI_PERIOD: Duration = Duration::from_secs(5);

pub async fn run() {
    awkernel_async_lib::spawn(
        APP_NAME.into(),
        test_dvfs(),
        awkernel_async_lib::scheduler::SchedulerType::PrioritizedFIFO(0),
    )
    .await;
}

unsafe fn try_set_cpu_freq(freq: u64) -> Result<()> {
    match set_cpu_freq(freq) {
        Ok(_) => Ok(()),
        Err(e) => {
            log::warn!(
                "Failed to set CPU frequency: {:?}. Trying with global frequency...",
                e
            );
            unsafe { set_global_freq(freq) }
        }
    }
}

async fn test_dvfs() {
    let max = match get_max_cpu_freq() {
        Ok(freq) => freq,
        Err(e) => {
            log::error!("Failed to get max CPU frequency: {:?}", e);
            return;
        }
    };
    let min = match get_min_cpu_freq() {
        Ok(freq) => freq,
        Err(e) => {
            log::error!("Failed to get min CPU frequency: {:?}", e);
            return;
        }
    };

    let mut now = Time::now();
    loop {
        let cpuid = awkernel_lib::cpu::cpu_id();

        // Maximum frequency.
        if let Err(e) = unsafe { try_set_cpu_freq(max) } {
            log::error!("Failed to set CPU frequency: {:?}", e);
            return;
        }

        let start = awkernel_async_lib::time::Time::now();

        for _ in 0..NUM_LOOP {
            core::hint::black_box(());
        }

        let t = start.elapsed();

        let current = match get_curr_cpu_freq() {
            Ok(freq) => freq,
            Err(e) => {
                log::error!("Failed to get current CPU frequency: {:?}", e);
                return;
            }
        };

        log::debug!("cpuid = {cpuid}, current = {current}, expected = {max}, time = {t:?}");

        awkernel_async_lib::sleep_until(now + SEMI_PERIOD).await;

        let cpuid = awkernel_lib::cpu::cpu_id();

        // Minimum frequency.
        if let Err(e) = unsafe { try_set_cpu_freq(min) } {
            log::error!("Failed to set CPU frequency: {:?}", e);
            return;
        }

        let start = awkernel_async_lib::time::Time::now();

        for _ in 0..NUM_LOOP {
            core::hint::black_box(());
        }

        let t = start.elapsed();

        let current = match get_curr_cpu_freq() {
            Ok(freq) => freq,
            Err(e) => {
                log::error!("Failed to get current CPU frequency: {:?}", e);
                return;
            }
        };

        log::debug!("cpuid = {cpuid}, current = {current}, expected = {min}, time = {t:?}");

        awkernel_async_lib::sleep_until(now + 2 * SEMI_PERIOD).await;
        now += 2 * SEMI_PERIOD;
    }
}
