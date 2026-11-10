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
const SAMPLE_PERIOD: Duration = Duration::from_secs(1);

#[cfg(all(target_arch = "x86_64", target_os = "none", feature = "energy"))]
mod energy;

pub async fn run() {
    let mut cpu_set = CpuSet::empty();
    cpu_set.insert(TEST_CPU);

    awkernel_async_lib::spawn(
        APP_NAME.into(),
        test_dvfs(),
        awkernel_async_lib::scheduler::SchedulerType::ClusteredEDF(DEADLINE, cpu_set),
    )
    .await;

    #[cfg(all(target_arch = "x86_64", target_os = "none", feature = "energy"))]
    awkernel_async_lib::spawn(
        energy::APP_NAME.into(),
        energy::measure_energy(),
        awkernel_async_lib::scheduler::SchedulerType::ClusteredEDF(DEADLINE, cpu_set),
    )
    .await;

    awkernel_async_lib::spawn(
        "test DVFS measurements".into(),
        measure_dvfs(),
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
    let cpuid = awkernel_lib::cpu::cpu_id();
    let min = get_min_cpu_freq()?;
    let max = get_max_cpu_freq()?;
    log::info!("CPU#{cpuid}: min = {min} Hz, max = {max} Hz");

    let mut next = Instant::now();
    let mut high = true;
    loop {
        let target = if high { max } else { min };
        unsafe { try_set_cpu_freq(target) }?;
        log::info!("CPU#{cpuid}: set frequency = {target} Hz");
        awkernel_lib::delay::wait_millisec(10); // Settle time

        next += SEMI_PERIOD;
        awkernel_async_lib::sleep_until(next).await;
        high = !high;
    }
}

async fn measure_dvfs() -> Result<()> {
    let mut next = Instant::now() + SAMPLE_PERIOD;
    loop {
        awkernel_async_lib::sleep_until(next).await;
        next += SAMPLE_PERIOD;

        let cpuid = awkernel_lib::cpu::cpu_id();

        // Measure the current CPU frequency while keeping interrupts disabled.
        let int_guard = awkernel_lib::interrupt::InterruptGuard::new();
        let current = get_curr_cpu_freq()?;
        let start = Instant::now();
        for _ in 0..NUM_LOOP {
            core::hint::black_box(());
        }
        let t = start.elapsed();
        drop(int_guard);

        log::info!("CPU#{cpuid}: measured frequency = {current} Hz, black-box delay = {t:?}");
    }
}
