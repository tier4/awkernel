#![no_std]
extern crate alloc;

mod parse_yaml;

use alloc::borrow::Cow;
use alloc::format;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use awkernel_async_lib::dag::create_dag;
use awkernel_async_lib::dag::finish_create_dags;
use awkernel_async_lib::dag::Dag;
use awkernel_async_lib::scheduler::SchedulerType;
use awkernel_async_lib::sleep;
use awkernel_lib::delay::wait_millisec;
use core::time::Duration;

use parse_yaml::DagData;

static TIME_UNIT: TimeUnit = TimeUnit::Milliseconds;

#[allow(dead_code)]
enum TimeUnit {
    Seconds,
    Milliseconds,
    Microseconds,
    Nanoseconds,
}

// A newline is required at the end due to yaml_peg specification.
// If you have multiple files, define a `const` for each.
// TODO: to be removed after filesystem implementation.
const DAG_FILE_0: &'static str = concat!(include_str!("../../../../DAGs/dag_0.yaml"), "\n");
const DAG_FILE_1: &'static str = concat!(include_str!("../../../../DAGs/dag_1.yaml"), "\n");

fn convert_duration(duration: u64) -> Duration {
    match TIME_UNIT {
        TimeUnit::Seconds => Duration::from_secs(duration),
        TimeUnit::Milliseconds => Duration::from_millis(duration),
        TimeUnit::Microseconds => Duration::from_micros(duration),
        TimeUnit::Nanoseconds => Duration::from_nanos(duration),
    }
}

fn create_reactor_name(dag_id: u32, node_id: u32) -> Cow<'static, str> {
    Cow::from(format!("dag_{}_node_{}", dag_id, node_id))
}

fn create_sub_topics(dag_id: u32, node_id: u32, in_links: &Vec<u32>) -> Vec<Cow<'static, str>> {
    let mut topics = vec![];
    in_links.iter().for_each(|link| {
        topics.push(Cow::from(format!(
            "dag_{}_node_{}_{}",
            dag_id, link, node_id
        )));
    });
    topics
}

fn create_pub_topics(dag_id: u32, node_id: u32, out_links: &Vec<u32>) -> Vec<Cow<'static, str>> {
    let mut topics = vec![];
    out_links.iter().for_each(|link| {
        topics.push(Cow::from(format!(
            "dag_{}_node_{}_{}",
            dag_id, node_id, link
        )));
    });
    topics
}

async fn generate_dag(dag_data: DagData) -> Arc<Dag> {
    let dag = create_dag();
    let dag_id = dag.get_id();

    log::debug!("Creating dag {}", dag_id);

    for node in dag_data.get_nodes() {
        let node_id = node.get_id();
        if node.is_source() {
            let execution_time = node.get_execution_time().clone();
            let out_links = node.get_out_links().clone();
            let period = node.get_period().unwrap().clone();

            let reactor_name = create_reactor_name(dag_id, node_id);
            let pub_topics = create_pub_topics(dag_id, node_id, &out_links);

            dag.spawn_periodic_reactor::<_, (i32,)>(
                reactor_name,
                move || -> (i32,) {
                    let _ = sleep(convert_duration(execution_time));
                    log::debug!("value={}", execution_time);
                    (execution_time as i32,)
                },
                pub_topics,
                SchedulerType::FIFO,
                convert_duration(period.clone()),
            )
            .await;
        } else if node.is_sink() {
            let execution_time = node.get_execution_time().clone();
            let in_links = node.get_in_links().clone();
            let relative_deadline = node.get_end_to_end_deadline().unwrap().clone();

            let reactor_name = create_reactor_name(dag_id, node_id);
            let sub_topics = create_sub_topics(dag_id, node_id, &in_links);

            dag.spawn_sink_reactor::<_, (i32,)>(
                reactor_name,
                move |(_,): (i32,)| {
                    let _ = sleep(convert_duration(execution_time));
                    log::debug!("value={}", execution_time);
                },
                sub_topics,
                SchedulerType::FIFO,
                convert_duration(relative_deadline),
            )
            .await;
        } else {
            let execution_time = node.get_execution_time().clone();
            let in_links = node.get_in_links().clone();
            let out_links = node.get_out_links().clone();

            let reactor_name = create_reactor_name(dag_id, node_id);
            let sub_topics = create_sub_topics(dag_id, node_id, &in_links);
            let pub_topics = create_pub_topics(dag_id, node_id, &out_links);

            dag.spawn_reactor::<_, (i32,), (i32,)>(
                reactor_name,
                move |(a,): (i32,)| -> (i32,) {
                    let _ = sleep(convert_duration(execution_time));
                    log::debug!("value={}", a);
                    (a,)
                },
                sub_topics,
                pub_topics,
                SchedulerType::FIFO,
            )
            .await;
        }
    }

    dag
}

pub async fn run() {
    wait_millisec(1000);
    log::info!("Starting DAG generation...");
    let dag_files = [DAG_FILE_0, DAG_FILE_1];
    let dag_data = parse_yaml::parse_dags(&dag_files);
    match dag_data {
        Ok(dags_data) => {
            let mut gen_dags = vec![];
            for dag_data in dags_data {
                log::info!("Generating DAG...");
                let dag = generate_dag(dag_data).await;
                log::info!("DAG generation completed.");
                gen_dags.push(dag);
            }
            log::info!("Creating DAGs...");
            let _ = finish_create_dags(&gen_dags).await;
            log::info!("DAGs creation completed.");
        }
        Err(e) => match e {
            parse_yaml::ParseError::EmptyYaml => {
                log::error!("Empty YAML file.");
            }
            parse_yaml::ParseError::UnmatchedYaml => {
                log::error!("Unmatched YAML file.");
            }
            parse_yaml::ParseError::MultipleDocumentsFound => {
                log::error!("Multiple documents found in YAML file.");
            }
        },
    }
}
