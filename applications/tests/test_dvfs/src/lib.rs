#![no_std]

use core::{
    sync::atomic::{AtomicU64, AtomicUsize, Ordering},
    time::Duration,
};

use alloc::{format, vec::Vec};
use array_macro::array;
use awkernel_lib::dvfs::DesiredPerformance;

extern crate alloc;

const APP_NAME: &str = "test DVFS";
const NUM_CPU: usize = 14;
const NUM_TRIALS: usize = 100;
const NUM_BUSY_LOOP: usize = 1000000000;

static LATENCY: [[[AtomicU64; NUM_TRIALS]; 10]; NUM_CPU] =
    array![_ => array![_ => array![_ => AtomicU64::new(0); NUM_TRIALS]; 10]; NUM_CPU];

static COUNT: [[AtomicUsize; 10]; NUM_CPU] =
    array![_ => array![_ => AtomicUsize::new(0); 10]; NUM_CPU];
static TOTAL_COUNT: AtomicUsize = AtomicUsize::new(0);

pub async fn run() {
    for _ in 0..(awkernel_lib::cpu::num_cpu() - 2) {
        awkernel_async_lib::spawn(
            APP_NAME.into(),
            test_dvfs(),
            awkernel_async_lib::scheduler::SchedulerType::FIFO,
        )
        .await;
    }
}

async fn test_dvfs() {
    let end_count = (awkernel_lib::cpu::num_cpu() - 1) * NUM_TRIALS * 10;

    while TOTAL_COUNT.load(Ordering::Relaxed) + 1 < end_count {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        for i in 0..10 {
            awkernel_lib::dvfs::set_min_performance(10 * i);
            awkernel_lib::dvfs::set_max_performance(10 * i);
            awkernel_lib::dvfs::set_energy_efficiency(100);
            awkernel_lib::dvfs::set_desired_performance(DesiredPerformance::Auto);

            let elapsed = empty_loop();

            let count =
                COUNT[cpu_id][i as usize].fetch_add(1, core::sync::atomic::Ordering::Relaxed);
            if count < NUM_TRIALS {
                LATENCY[cpu_id][i as usize][count].store(
                    elapsed.as_micros() as u64,
                    core::sync::atomic::Ordering::Relaxed,
                );

                let total_count = TOTAL_COUNT.fetch_add(1, core::sync::atomic::Ordering::Relaxed);

                log::debug!("progress: {total_count} / {end_count}");

                if total_count + 1 == end_count {
                    print_latency();
                }
            }
        }

        awkernel_async_lib::r#yield().await;
    }
}

fn empty_loop() -> Duration {
    let t = awkernel_async_lib::time::Time::now();
    for _ in 0..NUM_BUSY_LOOP {
        core::hint::black_box(());
    }
    t.elapsed()
}

fn print_latency() {
    let mut result: [[Vec<u64>; 10]; NUM_CPU] =
        array![_ => array![_ => Vec::with_capacity(NUM_TRIALS); 10]; NUM_CPU];

    for (j, latency_cpu) in LATENCY.iter().enumerate() {
        for (k, latency) in latency_cpu.iter().enumerate() {
            let mut sum = 0;
            let mut min = u64::MAX;
            let mut max = 0;
            for usec in latency.iter() {
                let val = usec.load(core::sync::atomic::Ordering::Relaxed);
                if min > val {
                    min = val;
                }
                if max < val {
                    max = val;
                }
                sum += val;

                result[j][k].push(val);
            }
            let avg = sum / NUM_TRIALS as u64;

            let msg = format!(
                "CPU {j}: Performance {}: Average: {avg} us, Min: {min} us, Max: {max} us\r\n",
                k * 10
            );
            awkernel_lib::console::print(&msg);
        }
    }

    let result_json = serde_json::to_string(&result).unwrap();
    let result_str = format!("{result_json}\r\n");
    awkernel_lib::console::print(&result_str);
}
