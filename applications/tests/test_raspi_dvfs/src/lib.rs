#![no_std]

use awkernel_async_lib::{self, scheduler::SchedulerType, sleep, spawn, time::Time};
use awkernel_drivers::ic::raspi::{
    clock::{self, ClockId},
    temperature,
    voltage::{self, VoltageId},
};
use core::time::Duration;

extern crate alloc;

const NUM_LOOP: usize = 1000000;
const SAMPLE_PERIOD: Duration = Duration::from_secs(10);

/// ARM core frequencies (Hz) requested in turn on the Raspberry Pi.
const REQUESTED_HZ: [u32; 5] = [
    1_800_000_000,
    1_500_000_000,
    1_000_000_000,
    600_000_000,
    300_000_000,
];

pub async fn run() {
    let min_hz = clock::get_min_clock_rate_hz(ClockId::Arm);
    let max_hz = clock::get_max_clock_rate_hz(ClockId::Arm);
    let state = clock::get_clock_state(ClockId::Arm);
    let turbo = clock::get_turbo();
    let current_hz = clock::get_clock_rate_hz(ClockId::Arm);

    log::info!(
        "ARM clock: min = {min_hz:?}, max = {max_hz:?}, current = {current_hz:?}, state = {state:?}, turbo = {turbo:?}"
    );

    let min_uv = voltage::get_min_voltage_uv(VoltageId::Core);
    let max_uv = voltage::get_max_voltage_uv(VoltageId::Core);
    let baseline_uv = voltage::get_voltage_uv(VoltageId::Core);

    log::info!(
        "Core voltage: min = {min_uv:?} uV, max = {max_uv:?} uV, initial = {baseline_uv:?} uV"
    );

    spawn(
        "raspi frequency test".into(),
        test_frequency(),
        SchedulerType::PrioritizedFIFO(0),
    )
    .await;
    spawn(
        "raspi voltage test".into(),
        test_voltage(),
        SchedulerType::PrioritizedFIFO(0),
    )
    .await;
    spawn(
        "raspi temperature monitor".into(),
        test_temperature(),
        SchedulerType::PrioritizedFIFO(0),
    )
    .await;
}

/// Runs the fixed CPU workload and returns its elapsed time.
fn measure_workload() -> Duration {
    let start = Time::now();
    for _ in 0..NUM_LOOP {
        core::hint::black_box(());
    }
    start.elapsed()
}

async fn test_frequency() {
    loop {
        for requested_hz in REQUESTED_HZ {
            sleep(SAMPLE_PERIOD).await;

            let result = clock::set_clock_rate_hz(ClockId::Arm, requested_hz, true);
            let actual_hz = clock::get_clock_rate_hz(ClockId::Arm);
            let elapsed = measure_workload();
            let current = clock::get_clock_rate_hz(ClockId::Arm);
            let measured = clock::get_clock_rate_measured_hz(ClockId::Arm);

            log::info!(
                "result = {result:?}, actual = {actual_hz:?}, current = {current:?}, measured = {measured:?}, time = {elapsed:?}"
            );
            if result.is_err() || actual_hz.is_err() || current.is_err() || measured.is_err() {
                log::warn!("frequency sample had one or more mailbox errors");
            }
        }
    }
}

async fn test_voltage() {
    loop {
        sleep(SAMPLE_PERIOD).await;
        let voltage_uv = voltage::get_voltage_uv(VoltageId::Core);
        log::info!("Core voltage = {voltage_uv:?} uV");
        if voltage_uv.is_err() {
            log::warn!("voltage sample had a mailbox error");
        }
    }
}

async fn test_temperature() {
    let max_temperature = temperature::get_max_temperature_millicelsius();
    log::info!("maximum safe SoC temperature = {max_temperature:?} milli-Celsius");

    loop {
        let current_temperature = temperature::get_temperature_millicelsius();
        log::info!("SoC temperature = {current_temperature:?} milli-Celsius");
        sleep(SAMPLE_PERIOD).await;
    }
}
