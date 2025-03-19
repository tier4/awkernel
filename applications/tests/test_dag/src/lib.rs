#![no_std]
extern crate alloc;

use alloc::{borrow::Cow, vec};
use awkernel_async_lib::dag::{create_dag, finish_create_dags};
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_lib::{delay::wait_microsec, sync::mutex::MCSNode};
use core::time::Duration;

pub async fn run() {
    wait_microsec(1000000);

    let dag = create_dag();

    dag.spawn_periodic_reactor::<_, (i32,)>(
        "reactor_source_node".into(),
        || -> (i32,) {
            let number: i32 = 1;
            log::debug!("value={} in reactor_source_node", number);
            (number,)
        },
        vec![Cow::from("topic0")],
        SchedulerType::FIFO,
        Duration::from_secs(1),
    )
    .await;

    dag.spawn_reactor::<_, (i32,), (i32, i32)>(
        "reactor_node1".into(),
        |(a,): (i32,)| -> (i32, i32) {
            log::debug!("value={} in reactor_node1", a);
            (a, a)
        },
        vec![Cow::from("topic0")],
        vec![Cow::from("topic1"), Cow::from("topic2")],
        SchedulerType::FIFO,
    )
    .await;

    dag.spawn_reactor::<_, (i32,), (i32,)>(
        "reactor_node2".into(),
        |(a,): (i32,)| -> (i32,) {
            log::debug!("value={} in reactor_node2", a * 2);
            (a * 2,)
        },
        vec![Cow::from("topic1")],
        vec![Cow::from("topic3")],
        SchedulerType::FIFO,
    )
    .await;

    dag.spawn_reactor::<_, (i32,), (i32,)>(
        "reactor_node3".into(),
        |(a,): (i32,)| -> (i32,) {
            log::debug!("value={} in reactor_node3", a * 3);
            (a * 3,)
        },
        vec![Cow::from("topic2")],
        vec![Cow::from("topic4")],
        SchedulerType::FIFO,
    )
    .await;

    dag.spawn_reactor::<_, (i32, i32), ()>(
        "reactor_node4".into(),
        |(a, b): (i32, i32)| {
            log::debug!("value={} in reactor_node4", a + b);
        },
        vec![Cow::from("topic3"), Cow::from("topic4")],
        vec![],
        SchedulerType::FIFO,
    )
    .await;

    finish_create_dags(&[dag.clone()]).await;

    let mut node = MCSNode::new();
    let graph = dag.graph.lock(&mut node);

    log::debug!("graph:\n{:#?}", &*graph);
}
