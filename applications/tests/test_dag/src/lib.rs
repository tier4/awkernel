#![no_std]
extern crate alloc;

use alloc::{borrow::Cow, vec};
use awkernel_async_lib::dag::{create_dag, finish_create_dags};
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_lib::delay::wait_microsec;
use core::time::Duration;

const LOG_ENABLE: bool = false;

pub async fn run() {
    wait_microsec(1000000);

    let period = Duration::from_nanos(1000000000);
    let exe_time = (period.as_micros() as f64 * 0.1) as u64;

    log::debug!("period is {} [ns]", period.as_nanos());

    let dag = create_dag();

    dag.register_periodic_reactor::<_, (i32,)>(
        "reactor_source_node".into(),
        move || -> (i32,) {
            wait_microsec(exe_time);
            let number: i32 = 1;
            if LOG_ENABLE {
                log::debug!("value={number} in reactor_source_node");
            }
            (number,)
        },
        vec![Cow::from("topic0")],
        SchedulerType::PrioritizedFIFO(30),
        period,
    )
    .await;

    dag.register_reactor::<_, (i32,), (i32, i32)>(
        "reactor_node1".into(),
        |(a,): (i32,)| -> (i32, i32) {
            let value = a + 1;
            if LOG_ENABLE {
                log::debug!("value={value} in reactor_node1");
            }

            (value, value + 1)
        },
        vec![Cow::from("topic0")],
        vec![Cow::from("topic1"), Cow::from("topic2")],
        SchedulerType::PrioritizedFIFO(0),
    )
    .await;

    dag.register_reactor::<_, (i32,), (i32,)>(
        "reactor_node2".into(),
        |(a,): (i32,)| -> (i32,) {
            let value = a * 2;
            if LOG_ENABLE {
                log::debug!("value={value} in reactor_node2");
            }
            (value,)
        },
        vec![Cow::from("topic1")],
        vec![Cow::from("topic3")],
        SchedulerType::PrioritizedFIFO(0),
    )
    .await;

    dag.register_reactor::<_, (i32,), (i32,)>(
        "reactor_node3".into(),
        |(a,): (i32,)| -> (i32,) {
            let value = a * 3;
            if LOG_ENABLE {
                log::debug!("value={value} in reactor_node3");
            }
            (value,)
        },
        vec![Cow::from("topic2")],
        vec![Cow::from("topic4")],
        SchedulerType::PrioritizedFIFO(0),
    )
    .await;

    dag.register_sink_reactor::<_, (i32, i32)>(
        "reactor_node4".into(),
        |(a, b): (i32, i32)| {
            let value = a + b;
            if LOG_ENABLE {
                log::debug!("value={value} in reactor_node4");
            }
        },
        vec![Cow::from("topic3"), Cow::from("topic4")],
        SchedulerType::PrioritizedFIFO(0),
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
