use crate::parse_yaml::{DagData, NodeData};
use crate::time_unit::{convert_duration, simulated_execution_time};

use alloc::{borrow::Cow, format, sync::Arc, vec::Vec};
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
    NoInput(u32, u32),
    NoOutput(u32, u32),
    NoInOut(u32, u32),
    MisMatch(u32, u32),
}

fn create_reactor_name(dag_id: u32, node_id: u32) -> Cow<'static, str> {
    Cow::from(format!("dag{dag_id}_node{node_id}"))
}

fn create_sub_topics(dag_id: u32, node_id: u32, in_links: &[u32]) -> Vec<Cow<'static, str>> {
    let mut topics = Vec::with_capacity(in_links.len());
    in_links.iter().for_each(|link| {
        topics.push(Cow::from(format!("dag{dag_id}_path{link}-{node_id}")));
    });
    topics
}

fn create_pub_topics(dag_id: u32, node_id: u32, out_links: &[u32]) -> Vec<Cow<'static, str>> {
    let mut topics = Vec::with_capacity(out_links.len());
    out_links.iter().for_each(|link| {
        topics.push(Cow::from(format!("dag{dag_id}_path_{node_id}-{link}")));
    });
    topics
}

macro_rules! setup_node_registration {
    ($dag:expr, $node_data:expr) => {{
        let dag_id = $dag.get_id();
        let node_id = $node_data.get_id();
        let execution_time = $node_data.get_execution_time();
        let in_links = $node_data.get_in_links();
        let out_links = $node_data.get_out_links();
        let reactor_name = create_reactor_name(dag_id, node_id);
        let sub_topics = create_sub_topics(dag_id, node_id, &in_links);
        let pub_topics = create_pub_topics(dag_id, node_id, &out_links);
        let period = $node_data.get_period();
        let relative_deadline = $node_data.get_end_to_end_deadline();

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
    ($dag:expr, $node_data:expr, $sched_type:expr, $($T_out:ident),*) => {
        {
            let (execution_time, reactor_name, _, pub_topics, period, _) = setup_node_registration!($dag, $node_data);

            if [$(stringify!($T_out)),*].len() != pub_topics.len() {
                return Err(LinkNumError::MisMatch($dag.get_id(), $node_data.get_id()));
            }

            $dag.register_periodic_reactor::<_, ($($T_out,)*)>(
                reactor_name.clone(),
                move || -> ($($T_out,)*) {
                    simulated_execution_time(execution_time);

                    let outputs = ($(execution_time as $T_out,)*);
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
    node_data: &NodeData,
    sched_type: SchedulerType,
) -> Result<(), LinkNumError> {
    let out_links_len = node_data.get_out_links().len();

    match out_links_len {
        0 => Err(LinkNumError::NoOutput(dag.get_id(), node_data.get_id())),
        1 => register_source!(dag, node_data, sched_type, u64),
        2 => register_source!(dag, node_data, sched_type, u64, u64),
        3 => register_source!(dag, node_data, sched_type, u64, u64, u64),
        _ => Err(LinkNumError::Output(dag.get_id(), node_data.get_id())),
    }
}

macro_rules! register_sink {
    ($dag:expr, $node_data:expr, $sched_type:expr, $($T_in:ident),*) => {
        {
            let (execution_time, reactor_name, sub_topics, _, _, relative_deadline) = setup_node_registration!($dag, $node_data);

            if [$(stringify!($T_in)),*].len() != sub_topics.len() {
                return Err(LinkNumError::MisMatch($dag.get_id(), $node_data.get_id()));
            }

            $dag.register_sink_reactor::<_, ($($T_in,)*)>(
                reactor_name.clone(),
                move |inputs: ($($T_in,)*)| {
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
    node_data: &NodeData,
    sched_type: SchedulerType,
) -> Result<(), LinkNumError> {
    let in_links_len = node_data.get_in_links().len();

    match in_links_len {
        0 => Err(LinkNumError::NoInput(dag.get_id(), node_data.get_id())),
        1 => register_sink!(dag, node_data, sched_type, u64),
        2 => register_sink!(dag, node_data, sched_type, u64, u64),
        3 => register_sink!(dag, node_data, sched_type, u64, u64, u64),
        _ => Err(LinkNumError::Input(dag.get_id(), node_data.get_id())),
    }
}

macro_rules! register_intermediate {
    ($dag:expr, $node_data:expr, $sched_type:expr, $($T_in:ident),*; $($T_out:ident),*) => {
        {
            let (execution_time, reactor_name, sub_topics, pub_topics, _, _) = setup_node_registration!($dag, $node_data);

            if [$(stringify!($T_in)),*].len() != sub_topics.len() {
                return Err(LinkNumError::MisMatch($dag.get_id(), $node_data.get_id()));
            }
            if [$(stringify!($T_out)),*].len() != pub_topics.len() {
                return Err(LinkNumError::MisMatch($dag.get_id(), $node_data.get_id()));
            }

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
    node_data: &NodeData,
    sched_type: SchedulerType,
) -> Result<(), LinkNumError> {
    let dag_id = dag.get_id();
    let node_id = node_data.get_id();
    let in_links_len = node_data.get_in_links().len();
    let out_links_len = node_data.get_out_links().len();

    match (in_links_len, out_links_len) {
        (0, 0) => Err(LinkNumError::NoInOut(dag_id, node_id)),
        (1, 1) => register_intermediate!(dag, node_data, sched_type, u64; u64),
        (1, 2) => register_intermediate!(dag, node_data, sched_type, u64; u64, u64),
        (1, 3) => register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64),
        (2, 1) => register_intermediate!(dag, node_data, sched_type, u64, u64; u64),
        (2, 2) => register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64),
        (2, 3) => register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64),
        (3, 1) => register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64),
        (3, 2) => register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64),
        (3, 3) => register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64),
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
    use alloc::vec;

    #[test]
    fn test_create_reactor_name() {
        let dag_id = 1;
        let node_id = 2;
        let expected_name = Cow::from("dag1_node2");
        let reactor_name = create_reactor_name(dag_id, node_id);
        assert_eq!(reactor_name, expected_name);
    }

    #[test]
    fn test_create_sub_topics() {
        let dag_id = 1;
        let node_id = 2;
        let in_links = vec![3, 4];
        let expected_topics = vec![Cow::from("dag1_path_3-2"), Cow::from("dag1_path_4-2")];
        let sub_topics = create_sub_topics(dag_id, node_id, &in_links);
        assert_eq!(sub_topics, expected_topics);
    }

    #[test]
    fn test_create_pub_topics() {
        let dag_id = 1;
        let node_id = 2;
        let out_links = vec![3, 4];
        let expected_topics = vec![Cow::from("dag1_path_2-3"), Cow::from("dag1_path_2-4")];
        let pub_topics = create_pub_topics(dag_id, node_id, &out_links);
        assert_eq!(pub_topics, expected_topics);
    }
}
