use crate::parse_yaml::{DagData, NodeData};
use crate::time_unit::{convert_duration, simulated_execution_time};

use alloc::{borrow::Cow, format, sync::Arc, vec, vec::Vec};
use awkernel_async_lib::{
    dag::{create_dag, Dag},
    scheduler::SchedulerType,
};

// TODO: Remove allow(dead_code).
#[allow(dead_code)]
// DAG ID, Node ID
enum LinkNumError {
    Input(u32, u32),
    Output(u32, u32),
    InOut(u32, u32),
    NoLink(u32, u32),
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

macro_rules! setup_node_registration {
    ($dag:expr, $node:expr) => {{
        let dag_id = $dag.get_id();
        let node_id = $node.get_id();
        let execution_time = $node.get_execution_time();
        let in_links = $node.get_in_links();
        let out_links = $node.get_out_links();
        let reactor_name = create_reactor_name(dag_id, node_id);
        let sub_topics = create_sub_topics(dag_id, node_id, &in_links);
        let pub_topics = create_pub_topics(dag_id, node_id, &out_links);
        let period = $node.get_period();
        let relative_deadline = $node.get_end_to_end_deadline();

        (
            execution_time,
            reactor_name,
            sub_topics,
            pub_topics,
            period,
            relative_deadline,
        )
    }};
}

macro_rules! register_source {
    ($dag:expr, $node:expr, $sched_type:expr, $($T:ident),*) => {
        {
            let (execution_time, reactor_name, _, pub_topics, period, _) = setup_node_registration!($dag, $node);

            $dag.register_periodic_reactor::<_, ($($T,)*)>(
                reactor_name.clone(),
                move || -> ($($T,)*) {
                    simulated_execution_time(execution_time);

                    let outputs = ($(execution_time as $T,)*);
                    log::debug!("name: {reactor_name}, outputs: {outputs:?}");
                    outputs
                },
                pub_topics,
                $sched_type,
                convert_duration(period.expect("Source node's period should always be Some.")),
            ).await;
            Ok(())
        }
    };
}

async fn register_source_node(
    dag: Arc<Dag>,
    node: &NodeData,
    sched_type: SchedulerType,
) -> Result<(), LinkNumError> {
    let out_links_len = node.get_out_links().len();

    match out_links_len {
        0 => unreachable!("`is_source()` ensures that `out_links_len` is >= 1"),
        1 => register_source!(dag, node, sched_type, u64),
        2 => register_source!(dag, node, sched_type, u64, u64),
        3 => register_source!(dag, node, sched_type, u64, u64, u64),
        _ => Err(LinkNumError::Input(dag.get_id(), node.get_id())),
    }
}

macro_rules! register_sink {
    ($dag:expr, $node:expr, $sched_type:expr, $($T:ident),*) => {
        {
            let (execution_time, reactor_name, sub_topics, _, _, relative_deadline) = setup_node_registration!($dag, $node);

            $dag.register_sink_reactor::<_, ($($T,)*)>(
                reactor_name.clone(),
                move |inputs: ($($T,)*)| {
                    simulated_execution_time(execution_time);
                    log::debug!("name: {reactor_name}, inputs: {inputs:?}");
                },
                sub_topics,
                $sched_type,
                convert_duration(relative_deadline.expect("Sink node's relative_deadline should always be Some.")),
            ).await;
            Ok(())
        }
    };
}

async fn register_sink_node(
    dag: Arc<Dag>,
    node: &NodeData,
    sched_type: SchedulerType,
) -> Result<(), LinkNumError> {
    let in_links_len = node.get_in_links().len();

    match in_links_len {
        0 => unreachable!("`is_sink()` ensures that `in_links_len` is >= 1."),
        1 => register_sink!(dag, node, sched_type, u64),
        2 => register_sink!(dag, node, sched_type, u64, u64),
        3 => register_sink!(dag, node, sched_type, u64, u64, u64),
        _ => Err(LinkNumError::Output(dag.get_id(), node.get_id())),
    }
}

macro_rules! register_intermediate {
    ($dag:expr, $node:expr, $sched_type:expr, $($T_in:ident),*; $($T_out:ident),*) => {
        {
            let (execution_time, reactor_name, sub_topics, pub_topics, _, _) = setup_node_registration!($dag, $node);

            $dag.register_reactor::<_, ($($T_in,)*), ($($T_out,)*)>(
                reactor_name.clone(),
                move |inputs: ($($T_in,)*)| -> ($($T_out,)*) {
                    simulated_execution_time(execution_time);
                    let outputs = ($(execution_time as $T_out,)*);
                    log::debug!("name: {reactor_name}, inputs: {inputs:?}, outputs: {outputs:?}");
                    outputs
                },
                sub_topics,
                pub_topics,
                $sched_type,
            ).await;
            Ok(())
        }
    };
}

async fn register_intermediate_node(
    dag: Arc<Dag>,
    node: &NodeData,
    sched_type: SchedulerType,
) -> Result<(), LinkNumError> {
    let dag_id = dag.get_id();
    let node_id = node.get_id();
    let in_links_len = node.get_in_links().len();
    let out_links_len = node.get_out_links().len();

    match (in_links_len, out_links_len) {
        (0, 0) => Err(LinkNumError::NoLink(dag_id, node_id)),
        (0, _) => unreachable!("Sink node must be registered by register_sink_node()"),
        (_, 0) => unreachable!("Source node must be registered by register_source_node()"),
        (1, 1) => register_intermediate!(dag, node, sched_type, u64; u64),
        (1, 2) => register_intermediate!(dag, node, sched_type, u64; u64, u64),
        (1, 3) => register_intermediate!(dag, node, sched_type, u64; u64, u64, u64),
        (2, 1) => register_intermediate!(dag, node, sched_type, u64, u64; u64),
        (2, 2) => register_intermediate!(dag, node, sched_type, u64, u64; u64, u64),
        (2, 3) => register_intermediate!(dag, node, sched_type, u64, u64; u64, u64, u64),
        (3, 1) => register_intermediate!(dag, node, sched_type, u64, u64, u64; u64),
        (3, 2) => register_intermediate!(dag, node, sched_type, u64, u64, u64; u64, u64),
        (3, 3) => register_intermediate!(dag, node, sched_type, u64, u64, u64; u64, u64, u64),
        (i, o) if i > 3 && o > 3 => Err(LinkNumError::InOut(dag_id, node_id)),
        (i, _) if i > 3 => Err(LinkNumError::Input(dag_id, node_id)),
        (_, o) if o > 3 => Err(LinkNumError::Output(dag_id, node_id)),
        _ => unreachable!(),
    }
}

// TODO: Remove allow(dead_code).
#[allow(dead_code)]
async fn build_dag_structure(
    dag_data: DagData,
    sched_type: SchedulerType,
) -> Result<Arc<Dag>, LinkNumError> {
    let dag = create_dag();

    for node in dag_data.get_nodes() {
        if node.is_source() {
            register_source_node(dag.clone(), node, sched_type).await?;
        } else if node.is_sink() {
            register_sink_node(dag.clone(), node, sched_type).await?;
        } else {
            register_intermediate_node(dag.clone(), node, sched_type).await?;
        }
    }

    Ok(dag)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_yaml::parse_dags;

    #[test]
    fn test_create_sub_topics() {
        let dag_id = 1;
        let node_id = 2;
        let in_links = vec![3, 4];
        let expected_topics = vec![Cow::from("dag_1_node_3_2"), Cow::from("dag_1_node_4_2")];
        let sub_topics = create_sub_topics(dag_id, node_id, &in_links);
        assert_eq!(sub_topics, expected_topics);
    }

    #[test]
    fn test_create_pub_topics() {
        let dag_id = 1;
        let node_id = 2;
        let out_links = vec![3, 4];
        let expected_topics = vec![Cow::from("dag_1_node_2_3"), Cow::from("dag_1_node_2_4")];
        let pub_topics = create_pub_topics(dag_id, node_id, &out_links);
        assert_eq!(pub_topics, expected_topics);
    }
}
