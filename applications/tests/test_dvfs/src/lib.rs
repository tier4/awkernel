#![no_std]

use core::{
    sync::atomic::{AtomicU64, AtomicUsize, Ordering, fence},
    time::Duration,
};

use alloc::{format, vec::Vec};
use array_macro::array;
use awkernel_lib::{
    dvfs::DesiredPerformance,
    sync::{mcs::MCSNode, mutex::Mutex},
};

extern crate alloc;

mod nbody;

const NUM_CPU: usize = 14;
const NUM_TRIALS_LATENCY: usize = 100;
const NUM_BUSY_LOOP: usize = 1000000000;

static LATENCY: [[[AtomicU64; NUM_TRIALS_LATENCY]; 11]; NUM_CPU] =
    array![_ => array![_ => array![_ => AtomicU64::new(0); NUM_TRIALS_LATENCY]; 11]; NUM_CPU];

static COUNT: [[AtomicUsize; 11]; NUM_CPU] =
    array![_ => array![_ => AtomicUsize::new(0); 11]; NUM_CPU];
static TOTAL_COUNT: AtomicUsize = AtomicUsize::new(0);

pub async fn run() {
    let mut waiter = Vec::with_capacity(awkernel_lib::cpu::num_cpu() - 2);

    for _ in 0..(awkernel_lib::cpu::num_cpu() - 2) {
        let w = awkernel_async_lib::spawn(
            "test_latency_diff".into(),
            test_latency_diff(),
            awkernel_async_lib::scheduler::SchedulerType::FIFO,
        )
        .await;

        waiter.push(w);
    }

    for w in waiter {
        let _ = w.join().await;
    }

    let mut waiter = Vec::with_capacity(awkernel_lib::cpu::num_cpu() - 2);

    for _ in 0..(awkernel_lib::cpu::num_cpu() - 2) {
        let w = awkernel_async_lib::spawn(
            "test_latency".into(),
            test_latency(),
            awkernel_async_lib::scheduler::SchedulerType::FIFO,
        )
        .await;

        waiter.push(w);
    }

    for w in waiter {
        let _ = w.join().await;
    }
}

async fn test_latency() {
    let end_count = (awkernel_lib::cpu::num_cpu() - 1) * NUM_TRIALS_LATENCY * 11;

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
            if count < NUM_TRIALS_LATENCY {
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
        array![_ => array![_ => Vec::with_capacity(NUM_TRIALS_LATENCY); 11]; NUM_CPU];

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
            let avg = sum / NUM_TRIALS_LATENCY as u64;

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

const NUM_TRIALS_LATENCY_DIFF: usize = 20;
static FREQ_LATENCY: [[Mutex<Vec<(u64, i64)>>; NUM_TRIALS_LATENCY_DIFF]; NUM_CPU] =
    array![_ => array![_ => Mutex::new(Vec::new()); NUM_TRIALS_LATENCY_DIFF]; NUM_CPU];
static TOTAL_COUNT_LATENCY_DIFF: AtomicUsize = AtomicUsize::new(0);
static N: usize = 500;

async fn test_latency_diff() {
    loop {
        awkernel_lib::dvfs::set_min_max_performance(10);
        awkernel_lib::dvfs::set_energy_efficiency(0);
        awkernel_lib::dvfs::set_desired_performance(DesiredPerformance::Auto);

        workload();

        let mut diff = Vec::with_capacity(N);

        awkernel_lib::dvfs::set_min_max_performance(100);
        awkernel_lib::dvfs::set_energy_efficiency(0);
        awkernel_lib::dvfs::set_desired_performance(DesiredPerformance::Auto);

        let t = awkernel_async_lib::time::Time::now();
        for _ in 0..N {
            let start = unsafe { core::arch::x86_64::_rdtsc() };
            fence(Ordering::AcqRel);
            for _ in 0..1000 {
                core::hint::black_box(());
            }
            fence(Ordering::AcqRel);
            let end = unsafe { core::arch::x86_64::_rdtsc() };
            diff.push((t.elapsed(), (end - start) as i64));
        }

        let mut result = Vec::new();

        for i in 0..(N - 1) {
            result.push((diff[i].0.as_nanos() as u64, diff[i + 1].1 - diff[i].1));
        }

        let cpu_id = awkernel_lib::cpu::cpu_id();
        for (i, r) in FREQ_LATENCY[cpu_id].iter().enumerate() {
            let mut node = MCSNode::new();
            let mut guard = r.lock(&mut node);
            if guard.is_empty() {
                *guard = result;
                drop(guard);

                let old_total = TOTAL_COUNT_LATENCY_DIFF.fetch_add(1, Ordering::Relaxed);

                log::debug!("{cpu_id}: {i}, {old_total}");

                if old_total == (NUM_CPU - 1) * NUM_TRIALS_LATENCY_DIFF - 1 {
                    print_latency_diff();
                }

                break;
            }
        }

        let total = TOTAL_COUNT_LATENCY_DIFF.load(Ordering::Relaxed);

        if total == (NUM_CPU - 1) * NUM_TRIALS_LATENCY_DIFF {
            break;
        }

        awkernel_async_lib::r#yield().await;
    }
}

fn print_latency_diff() {
    let mut result: [[Vec<(u64, i64)>; NUM_TRIALS_LATENCY_DIFF]; NUM_CPU] =
        array![_ => array![_ => Vec::new(); NUM_TRIALS_LATENCY_DIFF]; NUM_CPU];

    for (dst, src) in result.iter_mut().zip(FREQ_LATENCY.iter()) {
        for (dst, src) in dst.iter_mut().zip(src.iter()) {
            let mut node = MCSNode::new();
            let guard = src.lock(&mut node);

            *dst = guard.clone();
        }
    }

    let result_json = serde_json::to_string(&result).unwrap();
    let result_str = format!("{result_json}\r\n");
    awkernel_lib::console::print(&result_str);
}
