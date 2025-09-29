use crate::parse_yaml::{DagData, NodeData};
use crate::time_unit::{convert_duration, simulated_execution_time};

use alloc::{borrow::Cow, format, sync::Arc, vec::Vec};
use awkernel_async_lib::{
    dag::{Dag, create_dag},
    scheduler::SchedulerType,
    task::perf::record_run_time,
};

/// Represents errors related to the number of links for a node.
/// `(DAG ID, Node ID)` tuple to identify the specific DAG and node where the error occurred.
pub(crate) enum LinkNumError {
    Input(u32, u32),
    Output(u32, u32),
    InOut(u32, u32),
}

impl core::fmt::Display for LinkNumError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LinkNumError::Input(dag_id, node_id) => {
                write!(f, "DAG#{dag_id} Node#{node_id} has no input links")
            }
            LinkNumError::Output(dag_id, node_id) => {
                write!(f, "DAG#{dag_id} Node#{node_id} has no output links")
            }
            LinkNumError::InOut(dag_id, node_id) => {
                write!(f, "DAG#{dag_id} Node#{node_id} has no links")
            }
        }
    }
}

struct NodeRegistrationInfo {
    execution_time: u64,
    reactor_name: Cow<'static, str>,
    pub_topics: Vec<Cow<'static, str>>,
    sub_topics: Vec<Cow<'static, str>>,
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
        topics.push(Cow::from(format!("dag{dag_id}_path{node_id}-{link}")));
    });
    topics
}

fn setup_node_registration(dag_id: u32, node_data: &NodeData) -> NodeRegistrationInfo {
    let node_id = node_data.get_id();

    let execution_time = node_data.get_execution_time();
    let reactor_name = create_reactor_name(dag_id, node_id);
    let pub_topics = create_pub_topics(dag_id, node_id, node_data.get_out_links());
    let sub_topics = create_sub_topics(dag_id, node_id, node_data.get_in_links());

    NodeRegistrationInfo {
        execution_time,
        reactor_name,
        pub_topics,
        sub_topics,
    }
}

macro_rules! register_source {
    ($dag:expr, $node_data:expr, $sched_type:expr, $($T_out:ident),*) => {
        {
            let dag_id = $dag.get_id();
            let registration_info = setup_node_registration(dag_id, $node_data);

            let pub_topics = registration_info.pub_topics;

            assert!(
                [$(stringify!($T_out)),*].len() == pub_topics.len(),
                "LinkNumError::MisMatch: dag_id={:?}, node_id={:?}",
                dag_id,
                $node_data.get_id()
            );

            let reactor_name = registration_info.reactor_name;
            let execution_time = registration_info.execution_time;
            $dag.register_periodic_reactor::<_, ($($T_out,)*)>(
                reactor_name.clone(),
                move || -> ($($T_out,)*) {
                    simulated_execution_time(execution_time);

                    let outputs = ($(execution_time as $T_out,)*);
                    record_run_time(awkernel_async_lib::time::Time::now().uptime().as_nanos() as u64);
                    outputs
                },
                pub_topics,
                $sched_type,
                convert_duration($node_data.get_period().expect("Source node's period should always be Some.")),
            ).await;
            Ok(())
        }
    };
}

async fn register_source_node(
    dag: &Arc<Dag>,
    node_data: &NodeData,
    sched_type: SchedulerType,
) -> Result<(), LinkNumError> {
    let dag_id = dag.get_id();
    let node_id = node_data.get_id();

    let out_links_num = node_data.get_out_links().len();

    match out_links_num {
        1 => register_source!(dag, node_data, sched_type, u64),
        2 => register_source!(dag, node_data, sched_type, u64, u64),
        3 => register_source!(dag, node_data, sched_type, u64, u64, u64),
        _ => Err(LinkNumError::Output(dag_id, node_id)),
    }
}

macro_rules! register_sink {
    ($dag:expr, $node_data:expr, $sched_type:expr, $($T_in:ident),*) => {
        {
            let dag_id = $dag.get_id();
            let registration_info = setup_node_registration(dag_id, $node_data);

            let sub_topics = registration_info.sub_topics;

            assert!(
                [$(stringify!($T_in)),*].len() == sub_topics.len(),
                "LinkNumError::MisMatch: dag_id={:?}, node_id={:?}",
                dag_id,
                $node_data.get_id()
            );

            let reactor_name = registration_info.reactor_name;
            let execution_time = registration_info.execution_time;
            $dag.register_sink_reactor::<_, ($($T_in,)*)>(
                reactor_name.clone(),
                move |_inputs: ($($T_in,)*)| {
                    simulated_execution_time(execution_time);
                },
                sub_topics,
                $sched_type,
                convert_duration($node_data.get_end_to_end_deadline().expect("Sink node's relative_deadline should always be Some.")),
            ).await;
            Ok(())
        }
    };
}

async fn register_sink_node(
    dag: &Arc<Dag>,
    node_data: &NodeData,
    sched_type: SchedulerType,
) -> Result<(), LinkNumError> {
    let dag_id = dag.get_id();
    let node_id = node_data.get_id();

    let in_links_num = node_data.get_in_links().len();

    match in_links_num {
        1 => register_sink!(dag, node_data, sched_type, u64),
        2 => register_sink!(dag, node_data, sched_type, u64, u64),
        3 => register_sink!(dag, node_data, sched_type, u64, u64, u64),
        _ => Err(LinkNumError::Input(dag_id, node_id)),
    }
}

macro_rules! register_intermediate {
    ($dag:expr, $node_data:expr, $sched_type:expr, $($T_in:ident),*; $($T_out:ident),*) => {
        {
            let dag_id = $dag.get_id();
            let node_id = $node_data.get_id();

            let registration_info = setup_node_registration(dag_id, $node_data);

            let sub_topics = registration_info.sub_topics;
            let pub_topics = registration_info.pub_topics;

            assert!(
                [$(stringify!($T_in)),*].len() == sub_topics.len(),
                "LinkNumError::MisMatch (input topics): dag_id={:?}, node_id={:?}",
                dag_id,
                node_id
            );

            assert!(
                [$(stringify!($T_out)),*].len() == pub_topics.len(),
                "LinkNumError::MisMatch (output topics): dag_id={:?}, node_id={:?}",
                dag_id,
                node_id
            );

            let execution_time = registration_info.execution_time;
            let reactor_name = registration_info.reactor_name;
            $dag.register_reactor::<_, ($($T_in,)*), ($($T_out,)*)>(
                reactor_name.clone(),
                move |_inputs: ($($T_in,)*)| -> ($($T_out,)*) {
                    simulated_execution_time(execution_time);
                    let outputs = ($(execution_time as $T_out,)*);
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
    dag: &Arc<Dag>,
    node_data: &NodeData,
    sched_type: SchedulerType,
) -> Result<(), LinkNumError> {
    let dag_id = dag.get_id();
    let node_id = node_data.get_id();

    let in_links_num = node_data.get_in_links().len();
    let out_links_num = node_data.get_out_links().len();

    match (in_links_num, out_links_num) {
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

pub(super) async fn build_dag(
    dag_data: DagData,
    sched_type: SchedulerType,
) -> Result<Arc<Dag>, LinkNumError> {
    let dag = create_dag();

    for node in dag_data.get_nodes() {
        if node.is_source() {
            register_source_node(&dag, node, SchedulerType::PrioritizedFIFO(0)).await?;
        } else if node.is_sink() {
            register_sink_node(&dag, node, sched_type).await?;
        } else {
            register_intermediate_node(&dag, node, sched_type).await?;
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
        let expected_topics = vec![Cow::from("dag1_path3-2"), Cow::from("dag1_path4-2")];
        let sub_topics = create_sub_topics(dag_id, node_id, &in_links);
        assert_eq!(sub_topics, expected_topics);
    }

    #[test]
    fn test_create_pub_topics() {
        let dag_id = 1;
        let node_id = 2;
        let out_links = vec![3, 4];
        let expected_topics = vec![Cow::from("dag1_path2-3"), Cow::from("dag1_path2-4")];
        let pub_topics = create_pub_topics(dag_id, node_id, &out_links);
        assert_eq!(pub_topics, expected_topics);
    }
}
