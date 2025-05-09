#![no_std]
extern crate alloc;

mod parse_yaml;

use alloc::{borrow::Cow, format, sync::Arc, vec, vec::Vec};
use awkernel_async_lib::{
    dag::{self, create_dag, finish_create_dags, Dag},
    scheduler::SchedulerType,
};
use awkernel_lib::delay::wait_millisec;
use core::time::Duration;
use parse_yaml::{DagData, NodeData};

static TIME_UNIT: TimeUnit = TimeUnit::Milliseconds;

#[allow(dead_code)]
enum TimeUnit {
    Seconds,
    Milliseconds,
    Microseconds,
    Nanoseconds,
}

enum UnsupportedError {
    Input(u32),
    Output(u32),
    InputOutput(u32),
}

// A newline is required at the end due to yaml_peg specification.
// If you have multiple files, define a `const` for each.
// TODO: to be removed after filesystem implementation.
const DAG_FILE_0: &str = concat!(include_str!("../DAGs/dag_0.yaml"), "\n");
// const DAG_FILE_1: &str = concat!(include_str!("../../../../DAGs/dag_1.yaml"), "\n");

fn convert_duration(duration: u64) -> Duration {
    match TIME_UNIT {
        TimeUnit::Seconds => Duration::from_secs(duration),
        TimeUnit::Milliseconds => Duration::from_millis(duration),
        TimeUnit::Microseconds => Duration::from_micros(duration),
        TimeUnit::Nanoseconds => Duration::from_nanos(duration),
    }
}

fn convert_millisec(duration: u64) -> u64 {
    match TIME_UNIT {
        TimeUnit::Seconds => duration * 1000,
        TimeUnit::Milliseconds => duration,
        TimeUnit::Microseconds => duration / 1000,
        TimeUnit::Nanoseconds => duration / 1000000,
    }
}

fn create_reactor_name(dag_id: u32, node_id: u32) -> Cow<'static, str> {
    Cow::from(format!("dag_{dag_id}_node_{node_id}"))
}

fn create_sub_topics(dag_id: u32, node_id: u32, in_links: &[u32]) -> Vec<Cow<'static, str>> {
    let mut topics = vec![];
    in_links.iter().for_each(|link| {
        topics.push(Cow::from(format!("dag_{dag_id}_node_{link}_{node_id}")));
    });
    topics
}

fn create_pub_topics(dag_id: u32, node_id: u32, out_links: &[u32]) -> Vec<Cow<'static, str>> {
    let mut topics = vec![];
    out_links.iter().for_each(|link| {
        topics.push(Cow::from(format!("dag_{dag_id}_node_{node_id}_{link}")));
    });
    topics
}

macro_rules! spawn_source {
    ($dag:expr, $node:expr, $($T:ident),*) => {
        {
            let expected_arity = [$(stringify!($T)),*].len();

            let dag_id = $dag.get_id();
            let node_id = $node.get_id();
            let execution_time = $node.get_execution_time();
            let out_links = $node.get_out_links();
            let period = $node.get_period().unwrap();
            let reactor_name = create_reactor_name(dag_id, node_id);
            let pub_topics = create_pub_topics(dag_id, node_id, &out_links);

            if pub_topics.len() == expected_arity {
                $dag.spawn_periodic_reactor::<_, ($($T,)*)>(
                    reactor_name,
                    move || -> ($($T,)*) {
                        wait_millisec(convert_millisec(execution_time));

                        let outputs = ($(execution_time as $T,)*);

                        log::debug!(
                            "dag_id={}, node_id={}, out_num = {}, data={:?}",
                            dag_id,
                            node_id,
                            expected_arity,
                            outputs
                        );

                        outputs
                    },
                    pub_topics,
                    SchedulerType::FIFO,
                    convert_duration(period),
                ).await;
                Ok(())
            } else {
                unreachable!();
            }
        }
    };
}

async fn spawn_source_reactor(dag: Arc<Dag>, node: &NodeData) -> Result<(), UnsupportedError> {
    let out_links_len = node.get_out_links().len();
    match out_links_len {
        1 => spawn_source!(dag, node, u64),
        2 => spawn_source!(dag, node, u64, u64),
        3 => spawn_source!(dag, node, u64, u64, u64),
        _ => Err(UnsupportedError::Input(dag.get_id())),
    }
}

macro_rules! spawn_sink {
    ($dag:expr, $node:expr, $($T:ident),*) => {
        {
            let expected_arity = [$(stringify!($T)),*].len();

            let dag_id = $dag.get_id();
            let node_id = $node.get_id();
            let execution_time = $node.get_execution_time();
            let in_links = $node.get_in_links();
            let relative_deadline = $node.get_end_to_end_deadline()
                                        .unwrap();
            let reactor_name = create_reactor_name(dag_id, node_id);
            let sub_topics = create_sub_topics(dag_id, node_id, &in_links);

            if sub_topics.len() == expected_arity {
                $dag.spawn_sink_reactor::<_, ($($T,)*)>(
                    reactor_name,
                    move |inputs: ($($T,)*)| {
                        wait_millisec(convert_millisec(execution_time));
                        log::debug!(
                            "dag_id={}, node_id={}, in_num = {}, data={:?}",
                            dag_id,
                            node_id,
                            expected_arity,
                            inputs
                        );
                    },
                    sub_topics,
                    SchedulerType::FIFO,
                    convert_duration(relative_deadline),
                ).await;
                Ok(())
            } else {
                unreachable!();
            }
        }
    };
}

async fn spawn_sink_reactor(dag: Arc<Dag>, node: &NodeData) -> Result<(), UnsupportedError> {
    let in_links_len = node.get_in_links().len();
    match in_links_len {
        1 => spawn_sink!(dag, node, u64),
        2 => spawn_sink!(dag, node, u64, u64),
        3 => spawn_sink!(dag, node, u64, u64, u64),
        _ => Err(UnsupportedError::Output(dag.get_id())),
    }
}

macro_rules! spawn_normal {
    ($dag:expr, $node:expr, $($T_in:ident),*; $($T_out:ident),*) => {
        {
            let expected_arity_in = [$(stringify!($T_in)),*].len();
            let expected_arity_out = [$(stringify!($T_out)),*].len();

            let dag_id = $dag.get_id();
            let node_id = $node.get_id();
            let execution_time = $node.get_execution_time();
            let in_links = $node.get_in_links();
            let out_links = $node.get_out_links();
            let reactor_name = create_reactor_name(dag_id, node_id);
            let sub_topics = create_sub_topics(dag_id, node_id, &in_links);
            let pub_topics = create_pub_topics(dag_id, node_id, &out_links);

            if sub_topics.len() == expected_arity_in && pub_topics.len() == expected_arity_out {
                $dag.spawn_reactor::<_, ($($T_in,)*), ($($T_out,)*)>(
                    reactor_name,
                    move |inputs: ($($T_in,)*)| -> ($($T_out,)*) {
                        wait_millisec(convert_millisec(execution_time));
                        let outputs = ($(execution_time as $T_out,)*);
                        log::debug!(
                            " dag_id={}, node_id={}, in_num={}, out_num={}, in_data={:?}, out_data={:?}",
                            dag_id,
                            node_id,
                            expected_arity_in,
                            expected_arity_out,
                            inputs,
                            outputs
                        );

                        outputs
                    },
                    sub_topics,
                    pub_topics,
                    SchedulerType::FIFO,
                ).await;
                Ok(())
            } else {
                unreachable!();
            }
        }
    };
}

async fn spawn_normal_reactor(dag: Arc<Dag>, node: &NodeData) -> Result<(), UnsupportedError> {
    let in_links_len = node.get_in_links().len();
    let out_links_len = node.get_out_links().len();

    match (in_links_len, out_links_len) {
        (1, 1) => spawn_normal!(dag, node, u64; u64),
        (1, 2) => spawn_normal!(dag, node, u64; u64, u64),
        (1, 3) => spawn_normal!(dag, node, u64; u64, u64, u64),
        (2, 1) => spawn_normal!(dag, node, u64, u64; u64),
        (2, 2) => spawn_normal!(dag, node, u64, u64; u64, u64),
        (2, 3) => spawn_normal!(dag, node, u64, u64; u64, u64, u64),
        (3, 1) => spawn_normal!(dag, node, u64, u64, u64; u64),
        (3, 2) => spawn_normal!(dag, node, u64, u64, u64; u64, u64),
        (3, 3) => spawn_normal!(dag, node, u64, u64, u64; u64, u64, u64),
        _ => Err(UnsupportedError::InputOutput(dag.get_id())),
    }
}

async fn generate_dag(dag_data: DagData) -> Result<Arc<Dag>, UnsupportedError> {
    let dag = create_dag();

    for node in dag_data.get_nodes() {
        if node.is_source() {
            spawn_source_reactor(dag.clone(), node).await?;
        } else if node.is_sink() {
            spawn_sink_reactor(dag.clone(), node).await?;
        } else {
            spawn_normal_reactor(dag.clone(), node).await?;
        }
    }

    Ok(dag)
}

pub async fn run() {
    wait_millisec(1000);
    log::info!("Starting DAG generation...");
    let dag_files = [DAG_FILE_0];
    let dags_data = parse_yaml::parse_dags(&dag_files);
    match dags_data {
        Ok(dags_data) => {
            log::info!("Creating DAGs...");
            let mut gen_dags = vec![];

            for dag_data in dags_data {
                match generate_dag(dag_data).await {
                    Ok(dag) => {
                        gen_dags.push(dag);
                    }
                    Err(e) => match e {
                        UnsupportedError::Input(dag_id) => {
                            log::error!("Unsupported input arity for DAG ID: {dag_id}");
                        }
                        UnsupportedError::Output(dag_id) => {
                            log::error!("Unsupported output arity for DAG ID: {dag_id}");
                        }
                        UnsupportedError::InputOutput(dag_id) => {
                            log::error!("Unsupported arity for DAG ID: {dag_id}");
                        }
                    },
                }
            }

            let result = finish_create_dags(&gen_dags).await;

            match result {
                Ok(_) => {
                    log::info!("DAG generation completed successfully.");
                }
                Err(e) => match e {
                    dag::DagError::MissingPendingTasks(dag_id) => {
                        log::error!("Missing pending tasks for DAG ID: {dag_id}");
                    }
                    dag::DagError::NotWeaklyConnected(dag_id) => {
                        log::error!("DAG ID {dag_id} is not weakly connected.");
                    }
                    dag::DagError::ContainsCycle(dag_id) => {
                        log::error!("DAG ID {dag_id} contains a cycle.");
                    }
                },
            }
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
