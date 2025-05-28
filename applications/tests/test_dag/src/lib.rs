#![no_std]
extern crate alloc;

use alloc::{borrow::Cow, vec};
use awkernel_async_lib::dag::{create_dag, finish_create_dags};
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_lib::delay::wait_microsec;
use core::time::Duration;

const LOG_ENABLE: bool = true;

pub async fn run() {
    wait_microsec(1000000);

    let dag = create_dag();

    dag.register_periodic_reactor::<_, (i32,)>(
        "reactor_source_node".into(),
        || -> (i32,) {
            let number: i32 = 1;
            if LOG_ENABLE {
                log::debug!("value={number} in reactor_source_node");
            }
            (number,)
        },
        vec![Cow::from("topic0")],
        SchedulerType::FIFO,
        Duration::from_secs(1),
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
        SchedulerType::FIFO,
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
        SchedulerType::FIFO,
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
        SchedulerType::FIFO,
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
        SchedulerType::FIFO,
        Duration::from_secs(1),
    )
    .await;

    let _ = finish_create_dags(&[dag.clone()]).await;

    assert_eq!(dag.node_count(), 5);
    assert_eq!(dag.edge_count(), 5);
}
