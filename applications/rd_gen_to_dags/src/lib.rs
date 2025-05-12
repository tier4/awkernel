#![no_std]
extern crate alloc;

mod parse_yaml;
mod time_unit;

use alloc::{borrow::Cow, format, sync::Arc, vec, vec::Vec};
use awkernel_async_lib::{
    dag::{create_dag, Dag},
    scheduler::SchedulerType,
};
use awkernel_lib::delay::wait_millisec;
use parse_yaml::{DagData, NodeData};
use time_unit::{convert_duration, simulated_execution_time};

// TODO: Remove allow(dead_code).
#[allow(dead_code)]
enum UnsupportedError {
    Input(u32, u32),  // DAG ID, Node ID
    Output(u32, u32), // DAG ID, Node ID
    Both(u32, u32),   // DAG ID, Node ID
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

macro_rules! register_source {
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
                $dag.register_periodic_reactor::<_, ($($T,)*)>(
                    reactor_name,
                    move || -> ($($T,)*) {
                        simulated_execution_time(execution_time);

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

async fn register_source_node(dag: Arc<Dag>, node: &NodeData) -> Result<(), UnsupportedError> {
    let out_links_len = node.get_out_links().len();
    match out_links_len {
        1 => register_source!(dag, node, u64),
        2 => register_source!(dag, node, u64, u64),
        3 => register_source!(dag, node, u64, u64, u64),
        _ => Err(UnsupportedError::Input(dag.get_id(), node.get_id())),
    }
}

macro_rules! register_sink {
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
                $dag.register_sink_reactor::<_, ($($T,)*)>(
                    reactor_name,
                    move |inputs: ($($T,)*)| {
                        simulated_execution_time(execution_time);
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

async fn register_sink_node(dag: Arc<Dag>, node: &NodeData) -> Result<(), UnsupportedError> {
    let in_links_len = node.get_in_links().len();
    match in_links_len {
        1 => register_sink!(dag, node, u64),
        2 => register_sink!(dag, node, u64, u64),
        3 => register_sink!(dag, node, u64, u64, u64),
        _ => Err(UnsupportedError::Output(dag.get_id(), node.get_id())),
    }
}

macro_rules! register_normal {
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
                $dag.register_reactor::<_, ($($T_in,)*), ($($T_out,)*)>(
                    reactor_name,
                    move |inputs: ($($T_in,)*)| -> ($($T_out,)*) {
                        simulated_execution_time(execution_time);
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

async fn register_node(dag: Arc<Dag>, node: &NodeData) -> Result<(), UnsupportedError> {
    let dag_id = dag.get_id();
    let node_id = node.get_id();
    let in_links_len = node.get_in_links().len();
    let out_links_len = node.get_out_links().len();

    if in_links_len > 3 && out_links_len > 3 {
        return Err(UnsupportedError::Both(dag_id, node_id));
    }
    if in_links_len > 3 {
        return Err(UnsupportedError::Input(dag_id, node_id));
    }
    if out_links_len > 3 {
        return Err(UnsupportedError::Output(dag_id, node_id));
    }

    match (in_links_len, out_links_len) {
        (1, 1) => register_normal!(dag, node, u64; u64),
        (1, 2) => register_normal!(dag, node, u64; u64, u64),
        (1, 3) => register_normal!(dag, node, u64; u64, u64, u64),
        (2, 1) => register_normal!(dag, node, u64, u64; u64),
        (2, 2) => register_normal!(dag, node, u64, u64; u64, u64),
        (2, 3) => register_normal!(dag, node, u64, u64; u64, u64, u64),
        (3, 1) => register_normal!(dag, node, u64, u64, u64; u64),
        (3, 2) => register_normal!(dag, node, u64, u64, u64; u64, u64),
        (3, 3) => register_normal!(dag, node, u64, u64, u64; u64, u64, u64),
        _ => unreachable!(),
    }
}

// TODO: Remove allow(dead_code).
#[allow(dead_code)]
async fn build_dag_structure(dag_data: DagData) -> Result<Arc<Dag>, UnsupportedError> {
    let dag = create_dag();

    for node in dag_data.get_nodes() {
        if node.is_source() {
            register_source_node(dag.clone(), node).await?;
        } else if node.is_sink() {
            register_sink_node(dag.clone(), node).await?;
        } else {
            register_node(dag.clone(), node).await?;
        }
    }

    Ok(dag)
}

pub async fn run() {
    wait_millisec(1000);
    log::info!("-- TODO: Implement the remaining DAG construction logic --");
}
