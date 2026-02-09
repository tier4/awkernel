#![no_std]
extern crate alloc;

use alloc::{borrow::Cow, vec, sync::Arc};
use awkernel_async_lib::dag::{create_dag, finish_create_dags};
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_lib::delay::wait_microsec;
use core::time::Duration;
use awkernel_async_lib::task::perf::get_period_count;

const LOG_ENABLE: bool = false;
const DATA_SIZE: usize = 65536;

pub async fn run() {
    wait_microsec(1000000);

    let period = Duration::from_nanos(1000000000);
    let exe_time = (period.as_micros() as f64 * 0.1) as u64;

    log::debug!("period is {} [ns]", period.as_nanos());

    let dag = create_dag();
    let dag_id = dag.get_id();

    dag.register_periodic_reactor::<_, ((Arc<[u8; DATA_SIZE]>, u32),)>(
        "reactor_source_node".into(),
        move || -> ((Arc<[u8; DATA_SIZE]>, u32),) {
            wait_microsec(exe_time);
            let data: Arc<[u8; DATA_SIZE]> = Arc::new([0; DATA_SIZE]);
            let period_id = get_period_count(dag_id as usize) as u32;
            if LOG_ENABLE {
                log::debug!("Sending data[0]={}, period_id={}, size={} in reactor_source_node", data[0], period_id, DATA_SIZE);
            }
            ((data, period_id),)
        },
        vec![Cow::from("topic0")],
        SchedulerType::GEDF(5),
        period,
    )
    .await;

    dag.register_reactor::<_, ((Arc<[u8; DATA_SIZE]>, u32),), ((Arc<[u8; DATA_SIZE]>, u32), (Arc<[u8; DATA_SIZE]>, u32))>(
        "reactor_node1".into(),
        move |((data, period),): ((Arc<[u8; DATA_SIZE]>, u32),)| -> ((Arc<[u8; DATA_SIZE]>, u32), (Arc<[u8; DATA_SIZE]>, u32)) {
            if LOG_ENABLE {
                log::debug!("Processing data[0]={}, period={}, size={} in reactor_node1", data[0], period, DATA_SIZE);
            }

            ((data.clone(), period), (data, period))
        },
        vec![Cow::from("topic0")],
        vec![Cow::from("topic1"), Cow::from("topic2")],
        SchedulerType::GEDF(10),
    )
    .await;

    dag.register_reactor::<_, ((Arc<[u8; DATA_SIZE]>, u32),), ((Arc<[u8; DATA_SIZE]>, u32),)>(
        "reactor_node2".into(),
        |((data, period),): ((Arc<[u8; DATA_SIZE]>, u32),)| -> ((Arc<[u8; DATA_SIZE]>, u32),) {
            if LOG_ENABLE {
                log::debug!("Processing data[0]={}, period={}, size={} in reactor_node2", data[0], period, DATA_SIZE);
            }
            ((data, period),)
        },
        vec![Cow::from("topic1")],
        vec![Cow::from("topic3")],
        SchedulerType::GEDF(10),
    )
    .await;

    dag.register_reactor::<_, ((Arc<[u8; DATA_SIZE]>, u32),), ((Arc<[u8; DATA_SIZE]>, u32),)>(
        "reactor_node3".into(),
        |((data, period),): ((Arc<[u8; DATA_SIZE]>, u32),)| -> ((Arc<[u8; DATA_SIZE]>, u32),) {
            if LOG_ENABLE {
                log::debug!("Processing data[0]={}, period={}, size={} in reactor_node3", data[0], period, DATA_SIZE);
            }
            ((data, period),)
        },
        vec![Cow::from("topic2")],
        vec![Cow::from("topic4")],
        SchedulerType::GEDF(10),
    )
    .await;

    dag.register_sink_reactor::<_, ((Arc<[u8; DATA_SIZE]>, u32), (Arc<[u8; DATA_SIZE]>, u32))>(
        "reactor_node4".into(),
        |((data1, period1), (data2, period2)): ((Arc<[u8; DATA_SIZE]>, u32), (Arc<[u8; DATA_SIZE]>, u32))| {
            if LOG_ENABLE {
                log::debug!("Received data1[0]={}, data2[0]={}, period1={}, period2={}, size={} in reactor_node4", data1[0], data2[0], period1, period2, DATA_SIZE);
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
