//! Same DAG shape as `test_dag`, but every node is spawned with
//! `SchedulerType::ClusteredEDF` sharing one `CpuSet` instead of `GEDF`.
//!
//! This exists to check three things for the Federated Scheduling gap list
//! (item 6, static-CpuSet variant: dynamic CpuSet reassignment is out of
//! scope here, the whole DAG is just pinned to one fixed cluster up front):
//! - every node actually runs only on a core inside the assigned `CpuSet`
//! - execution time is measured precisely (see `(perf)` / `(trace)`)
//! - a task's DAG/node identity is visible (see `(task)`'s DAG column)

#![no_std]
extern crate alloc;

use alloc::{borrow::Cow, vec};
use awkernel_async_lib::dag::{create_dag, finish_create_dags};
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_lib::cpu::{cpu_id, CpuSet};
use awkernel_lib::delay::wait_microsec;
use core::time::Duration;

const LOG_ENABLE: bool = false;

/// All nodes of this DAG are confined to this cluster of cores.
fn cluster() -> CpuSet {
    CpuSet::empty().insert(1).insert(2).insert(3)
}

/// Log whether the current core is inside `cluster()`, tagged with the
/// reactor name so it is easy to grep in the boot log.
fn check_core(reactor_name: &str) {
    let actual = cpu_id();
    let set = cluster();
    if LOG_ENABLE{
        if set.contains(actual) {
        log::info!("clustered_dag: {reactor_name} ran on cpu {actual} [OK]");
        } else {
            log::error!("clustered_dag: {reactor_name} ran on cpu {actual}, expected in {set:?} [FAIL]");
        }
    }
}

pub async fn run() {
    wait_microsec(1_000_000);

    let period = Duration::from_nanos(1_000_000_000);
    let exe_time = (period.as_micros() as f64 * 0.1) as u64;

    log::debug!("period is {} [ns]", period.as_nanos());

    let dag = create_dag();
    let set = cluster();

    dag.register_periodic_reactor::<_, (i32,)>(
        "clustered_source_node".into(),
        move || -> (i32,) {
            check_core("clustered_source_node");
            wait_microsec(exe_time);
            let number: i32 = 1;
            if LOG_ENABLE {
                log::debug!("value={number} in clustered_source_node");
            }
            (number,)
        },
        vec![Cow::from("c_topic0")],
        SchedulerType::ClusteredEDF(5, set),
        period,
    )
    .await;

    dag.register_reactor::<_, (i32,), (i32, i32)>(
        "clustered_node1".into(),
        move |(a,): (i32,)| -> (i32, i32) {
            check_core("clustered_node1");
            let value = a + 1;
            if LOG_ENABLE {
                log::debug!("value={value} in clustered_node1");
            }
            (value, value + 1)
        },
        vec![Cow::from("c_topic0")],
        vec![Cow::from("c_topic1"), Cow::from("c_topic2")],
        SchedulerType::ClusteredEDF(10, set),
    )
    .await;

    dag.register_reactor::<_, (i32,), (i32,)>(
        "clustered_node2".into(),
        move |(a,): (i32,)| -> (i32,) {
            check_core("clustered_node2");
            let value = a * 2;
            if LOG_ENABLE {
                log::debug!("value={value} in clustered_node2");
            }
            (value,)
        },
        vec![Cow::from("c_topic1")],
        vec![Cow::from("c_topic3")],
        SchedulerType::ClusteredEDF(10, set),
    )
    .await;

    dag.register_reactor::<_, (i32,), (i32,)>(
        "clustered_node3".into(),
        move |(a,): (i32,)| -> (i32,) {
            check_core("clustered_node3");
            let value = a * 3;
            if LOG_ENABLE {
                log::debug!("value={value} in clustered_node3");
            }
            (value,)
        },
        vec![Cow::from("c_topic2")],
        vec![Cow::from("c_topic4")],
        SchedulerType::ClusteredEDF(10, set),
    )
    .await;

    dag.register_sink_reactor::<_, (i32, i32)>(
        "clustered_sink_node".into(),
        move |(a, b): (i32, i32)| {
            check_core("clustered_sink_node");
            let value = a + b;
            if LOG_ENABLE {
                log::debug!("value={value} in clustered_sink_node");
            }
        },
        vec![Cow::from("c_topic3"), Cow::from("c_topic4")],
        SchedulerType::ClusteredEDF(10, set),
        Duration::from_secs(1),
    )
    .await;

    let result = finish_create_dags(&[dag.clone()]).await;

    match result {
        Ok(_) => {
            log::info!("clustered_dag: DAG created successfully, cluster={set:?}");
        }
        Err(errors) => {
            log::error!("clustered_dag: failed to create DAG");
            for error in errors {
                log::error!("- {error}");
            }
        }
    }
}
