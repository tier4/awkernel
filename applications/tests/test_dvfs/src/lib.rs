#![no_std]

use core::{
    sync::atomic::{AtomicU64, AtomicUsize, Ordering, fence},
    time::Duration,
};

use alloc::{format, vec::Vec};
use array_macro::array;
use awkernel_lib::dvfs::DesiredPerformance;
use num_traits::abs;

extern crate alloc;

mod nbody;

const APP_NAME: &str = "test DVFS";
const NUM_CPU: usize = 14;
const NUM_TRIALS: usize = 100;
const NUM_BUSY_LOOP: usize = 1000000000;

static LATENCY: [[[AtomicU64; NUM_TRIALS]; 11]; NUM_CPU] =
    array![_ => array![_ => array![_ => AtomicU64::new(0); NUM_TRIALS]; 11]; NUM_CPU];

static COUNT: [[AtomicUsize; 11]; NUM_CPU] =
    array![_ => array![_ => AtomicUsize::new(0); 11]; NUM_CPU];
static TOTAL_COUNT: AtomicUsize = AtomicUsize::new(0);

pub async fn run() {
    for _ in 0..(awkernel_lib::cpu::num_cpu() - 2) {
        awkernel_async_lib::spawn(
            APP_NAME.into(),
            test_freq_latency(),
            awkernel_async_lib::scheduler::SchedulerType::FIFO,
        )
        .await;
    }
}

async fn test_dvfs() {
    let end_count = (awkernel_lib::cpu::num_cpu() - 1) * NUM_TRIALS * 11;

    while TOTAL_COUNT.load(Ordering::Relaxed) + 1 < end_count {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        for i in 0..=10 {
            awkernel_lib::dvfs::set_min_max_performance(10 * i);
            awkernel_lib::dvfs::set_energy_efficiency(0);
            awkernel_lib::dvfs::set_desired_performance(DesiredPerformance::Auto);

            warm_up();

            let elapsed = workload();

            log::debug!(
                "CPU {cpu_id}: Performance {}: Elapsed: {} [us]",
                i * 10,
                elapsed.as_micros()
            );

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

fn warm_up() {
    for _ in 0..(NUM_BUSY_LOOP) {
        core::hint::black_box(());
    }
}

fn workload() -> Duration {
    let t = awkernel_async_lib::time::Time::now();
    nbody::simulate();
    t.elapsed()
}

fn print_latency() {
    let mut result: [[Vec<u64>; 11]; NUM_CPU] =
        array![_ => array![_ => Vec::with_capacity(NUM_TRIALS); 11]; NUM_CPU];

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

async fn test_freq_latency() {
    loop {
        awkernel_lib::dvfs::set_min_max_performance(25);
        awkernel_lib::dvfs::set_energy_efficiency(0);
        awkernel_lib::dvfs::set_desired_performance(DesiredPerformance::Auto);

        warm_up();

        let mut diff = Vec::with_capacity(100000);

        awkernel_lib::dvfs::set_min_max_performance(100);
        awkernel_lib::dvfs::set_energy_efficiency(0);
        awkernel_lib::dvfs::set_desired_performance(DesiredPerformance::Auto);

        let t = awkernel_async_lib::time::Time::now();
        for _ in 0..100000 {
            let start = unsafe { core::arch::x86_64::_rdtsc() };
            fence(Ordering::AcqRel);
            for _ in 0..1000 {
                core::hint::black_box(());
            }
            fence(Ordering::AcqRel);
            let end = unsafe { core::arch::x86_64::_rdtsc() };
            diff.push((t.elapsed(), (end - start) as i64));
        }

        // let mut result = Vec::new();

        for i in 0..100 {
            // result.push((diff[i].0, diff[i + 1].1 - diff[i].1));
            if abs(diff[i + 1].1 - diff[i].1) > 100 {
                log::debug!("{i}: {:?}", diff[i + 1].1 - diff[i].1);
            }
        }

        // log::debug!("{result:?}");
    }
}
