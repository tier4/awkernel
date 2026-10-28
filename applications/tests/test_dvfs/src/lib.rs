#![no_std]

use awkernel_lib::{
    cpu::CpuSet,
    dvfs::{
        Result, get_curr_cpu_freq, get_max_cpu_freq, get_min_cpu_freq, set_cpu_freq,
        set_global_freq,
    },
    time::Instant,
};
use core::time::Duration;

extern crate alloc;

const APP_NAME: &str = "test DVFS";

/// The CPU where the test runs. CPU 0 is reserved for the primary core.
const TEST_CPU: usize = 1;
/// Relative deadline of the (otherwise irrelevant) EDF task, in milliseconds.
const DEADLINE: u64 = 1000;

const NUM_LOOP: usize = 1000000;
const SEMI_PERIOD: Duration = Duration::from_secs(5);

pub async fn run() {
    let mut cpu_set = CpuSet::empty();
    cpu_set.insert(TEST_CPU);

    awkernel_async_lib::spawn(
        APP_NAME.into(),
        test_dvfs(),
        awkernel_async_lib::scheduler::SchedulerType::ClusteredEDF(DEADLINE, cpu_set),
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

async fn test_dvfs() -> Result<()> {
    let mut now = Instant::now();
    loop {
        let cpuid = awkernel_lib::cpu::cpu_id();
        let min = get_min_cpu_freq()?;
        let max = get_max_cpu_freq()?;
        log::info!("CPU#{cpuid}: min = {min} Hz, max = {max} Hz");

        // Maximum frequency.
        log::info!("Setting CPU frequency to maximum: {max} Hz");
        unsafe { try_set_cpu_freq(max) }?;
        awkernel_lib::delay::wait_millisec(10); // Settle time

        let start = Instant::now();
        for _ in 0..NUM_LOOP {
            core::hint::black_box(());
        }
        let t = start.elapsed();
        let current = get_curr_cpu_freq()?;

        log::debug!("current = {current}, expected = {max}, time = {t:?}");

        awkernel_async_lib::sleep_until(now + SEMI_PERIOD).await;

        let cpuid = awkernel_lib::cpu::cpu_id();
        let min = get_min_cpu_freq()?;
        let max = get_max_cpu_freq()?;
        log::info!("CPU#{cpuid}: min = {min} Hz, max = {max} Hz");

        // Minimum frequency.
        log::info!("Setting CPU frequency to minimum: {min} Hz");
        unsafe { try_set_cpu_freq(min) }?;
        awkernel_lib::delay::wait_millisec(10); // Settle time

        let start = Instant::now();
        for _ in 0..NUM_LOOP {
            core::hint::black_box(());
        }
        let t = start.elapsed();
        let current = get_curr_cpu_freq()?;

        log::debug!("current = {current}, expected = {min}, time = {t:?}");

        awkernel_async_lib::sleep_until(now + 2 * SEMI_PERIOD).await;
        now += 2 * SEMI_PERIOD;
    }
}
