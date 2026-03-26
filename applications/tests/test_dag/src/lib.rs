#![no_std]
extern crate alloc;

use alloc::{borrow::Cow, vec};
use awkernel_async_lib::dag::{create_dag, finish_create_dags};
use awkernel_async_lib::scheduler::SchedulerType;
#[cfg(not(feature = "dag-no-period"))]
use awkernel_async_lib::task::perf::get_period_count;
use awkernel_lib::delay::wait_microsec;
use core::time::Duration;

const LOG_ENABLE: bool = true;
const DATA_SIZE: usize = 128;

// Conditional message type based on features
#[cfg(not(feature = "dag-no-period"))]
type DagMsg<T> = (T, u32);
#[cfg(feature = "dag-no-period")]
type DagMsg<T> = T;

// Conditional message packing/unpacking - dag-no-period フィーチャー有効時
#[cfg(not(feature = "dag-no-period"))]
fn pack_dag_msg<T>(value: T, period_id: u32) -> DagMsg<T> {
    (value, period_id)
}

#[cfg(not(feature = "dag-no-period"))]
fn unpack_dag_msg<T>(msg: DagMsg<T>) -> (T, u32) {
    msg
}

#[cfg(not(feature = "dag-no-period"))]
fn current_period_id(dag_id: u32) -> u32 {
    get_period_count(dag_id as usize) as u32
}

// dag-no-period フィーチャー無効時 (period_id は使わない)
#[cfg(feature = "dag-no-period")]
fn pack_dag_msg<T>(value: T, _period_id: u32) -> DagMsg<T> {
    value
}

#[cfg(feature = "dag-no-period")]
fn unpack_dag_msg<T>(msg: DagMsg<T>) -> (T, u32) {
    (msg, 0)
}

#[cfg(feature = "dag-no-period")]
fn current_period_id(_dag_id: u32) -> u32 {
    5
}

pub async fn run() {
    wait_microsec(1000000);

    let period = Duration::from_nanos(1000000000);
    let exe_time = (period.as_micros() as f64 * 0.1) as u64;

    log::debug!("period is {} [ns]", period.as_nanos());

    let dag = create_dag();
    let dag_id = dag.get_id();

    dag.register_periodic_reactor::<_, (DagMsg<i32>,)>(
        "reactor_source_node".into(),
        move || -> (DagMsg<i32>,) {
            wait_microsec(exe_time);
            let number: i32 = 1;
            let period_id = current_period_id(dag_id);
            if LOG_ENABLE {
                log::debug!("value={number} period={period_id} in reactor_source_node");
            }
            (pack_dag_msg(number, period_id),)
        },
        vec![Cow::from("topic0")],
        SchedulerType::GEDF(5),
        period,
    )
    .await;

    dag.register_reactor::<_, (DagMsg<i32>,), (DagMsg<i32>, DagMsg<i32>)>(
        "reactor_node1".into(),
        move |(msg,): (DagMsg<i32>,)| -> (DagMsg<i32>, DagMsg<i32>) {
            let (value, period) = unpack_dag_msg(msg);
            let result = value + 1;
            if LOG_ENABLE {
                log::debug!("value={result} in reactor_node1");
            }

            (
                pack_dag_msg(result, period),
                pack_dag_msg(result + 1, period),
            )
        },
        vec![Cow::from("topic0")],
        vec![Cow::from("topic1"), Cow::from("topic2")],
        SchedulerType::GEDF(10),
    )
    .await;

    dag.register_reactor::<_, (DagMsg<i32>,), (DagMsg<i32>,)>(
        "reactor_node2".into(),
        |(msg,): (DagMsg<i32>,)| -> (DagMsg<i32>,) {
            let (value, period) = unpack_dag_msg(msg);
            let result = value * 2;
            if LOG_ENABLE {
                log::debug!("value={result} in reactor_node2");
            }
            (pack_dag_msg(result, period),)
        },
        vec![Cow::from("topic1")],
        vec![Cow::from("topic3")],
        SchedulerType::GEDF(10),
    )
    .await;

    dag.register_reactor::<_, (DagMsg<i32>,), (DagMsg<i32>,)>(
        "reactor_node3".into(),
        |(msg,): (DagMsg<i32>,)| -> (DagMsg<i32>,) {
            let (value, period) = unpack_dag_msg(msg);
            let result = value * 3;
            if LOG_ENABLE {
                log::debug!("value={result} in reactor_node3");
            }
            (pack_dag_msg(result, period),)
        },
        vec![Cow::from("topic2")],
        vec![Cow::from("topic4")],
        SchedulerType::GEDF(10),
    )
    .await;

    dag.register_sink_reactor::<_, (DagMsg<i32>, DagMsg<i32>)>(
        "reactor_node4".into(),
        |(msg1, msg2): (DagMsg<i32>, DagMsg<i32>)| {
            let (value1, _period1) = unpack_dag_msg(msg1);
            let (value2, _period2) = unpack_dag_msg(msg2);
            let result = value1 + value2;
            if LOG_ENABLE {
                log::debug!("value={result} in reactor_node4");
            }
        },
        vec![Cow::from("topic3"), Cow::from("topic4")],
        SchedulerType::GEDF(10),
        Duration::from_secs(1),
    )
    .await;

    let result = finish_create_dags(&[dag.clone()]).await;

    match result {
        Ok(_) => {
            if LOG_ENABLE {
                log::info!("DAG created successfully");
            }
        }
        Err(errors) => {
            log::error!("Failed to create DAGs");
            for error in errors {
                log::error!("- {error}");
            }
        }
    }
}
