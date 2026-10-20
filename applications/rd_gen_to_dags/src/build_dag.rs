use crate::dag_stats::compute_dag_stats;
#[cfg(feature = "laxity")]
use crate::dag_stats::compute_node_laxity;
use crate::parse_yaml::{DagData, NodeData};
use crate::time_unit::{convert_duration, simulated_execution_time};

use alloc::{borrow::Cow, collections::BTreeMap, format, sync::Arc, vec::Vec};
#[cfg(not(feature = "vfed"))]
use awkernel_async_lib::dag_sched::policy::federated::FederatedAssignment;
#[cfg(feature = "vfed")]
use awkernel_async_lib::dag_sched::policy::vfed;
#[cfg(feature = "dagfluid")]
use awkernel_async_lib::dag_sched::resource::{self, ResourceError};
#[cfg(any(feature = "laxity", feature = "dagfluid"))]
use awkernel_async_lib::dag_sched::{
    metrics::DagMetrics,
    precondition::{self, Policy},
};
use awkernel_async_lib::{
    dag::{Dag, DagError, create_dag, record_build_failure},
    dag_sched::admission::AdmissionError,
    scheduler::SchedulerType,
};

#[cfg(any(
    all(feature = "vfed", feature = "laxity"),
    all(feature = "vfed", feature = "dagfluid"),
    all(feature = "laxity", feature = "dagfluid"),
))]
compile_error!(
    "features \"vfed\", \"laxity\", and \"dagfluid\" select mutually exclusive admission policies"
);

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

/// Errors that can prevent a DAG from being built: link-arity validation,
/// the DAG's own problems ([`DagError`]: missing timing, or a precondition
/// of the active admission policy, see
/// `awkernel_async_lib::dag_sched::precondition`), or the admission
/// policy's rejection ([`AdmissionError`]).
pub(crate) enum BuildDagError {
    LinkNum(LinkNumError),
    Dag(DagError),
    Admission(AdmissionError),
    /// `vfed::admit_batch` succeeded but `into_scheduler_type` returned
    /// `None` — should not happen for any `VFedAssignment` this crate's own
    /// admission call can produce (see that method's own doc), kept only so
    /// the conversion stays total rather than panicking on a should-never
    /// happen case.
    #[cfg(feature = "vfed")]
    VFedSchedulerTypeMissing(u32),
    /// Federated build: `build_dag` was called without the assignment the
    /// batch admission (`federated::admit_batch`) should have decided.
    #[cfg(not(any(feature = "vfed", feature = "laxity", feature = "dagfluid")))]
    FederatedNotAdmitted(u32),
}

impl core::fmt::Display for BuildDagError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BuildDagError::LinkNum(e) => write!(f, "{e}"),
            BuildDagError::Dag(e) => write!(f, "{e}"),
            BuildDagError::Admission(e) => write!(f, "{e}"),
            #[cfg(feature = "vfed")]
            BuildDagError::VFedSchedulerTypeMissing(dag_id) => write!(
                f,
                "DAG#{dag_id}: vfed admitted it but produced no SchedulerType"
            ),
            #[cfg(not(any(feature = "vfed", feature = "laxity", feature = "dagfluid")))]
            BuildDagError::FederatedNotAdmitted(dag_id) => write!(
                f,
                "DAG#{dag_id}: no federated batch-admission decision for this DAG"
            ),
        }
    }
}

impl From<LinkNumError> for BuildDagError {
    fn from(e: LinkNumError) -> Self {
        BuildDagError::LinkNum(e)
    }
}

impl From<DagError> for BuildDagError {
    fn from(e: DagError) -> Self {
        BuildDagError::Dag(e)
    }
}

impl From<AdmissionError> for BuildDagError {
    fn from(e: AdmissionError) -> Self {
        BuildDagError::Admission(e)
    }
}

#[cfg(feature = "dagfluid")]
impl From<ResourceError> for BuildDagError {
    fn from(e: ResourceError) -> Self {
        BuildDagError::Admission(AdmissionError::Resource(e))
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
                    // log::debug!("name: {reactor_name}, outputs: {outputs:?}");
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
        4 => register_source!(dag, node_data, sched_type, u64, u64, u64, u64),
        5 => register_source!(dag, node_data, sched_type, u64, u64, u64, u64, u64),
        6 => register_source!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64),
        7 => register_source!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64
        ),
        8 => register_source!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64
        ),
        9 => register_source!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64
        ),
        10 => register_source!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64
        ),
        11 => register_source!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64
        ),
        12 => register_source!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64
        ),
        13 => register_source!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64,
            u64
        ),
        14 => register_source!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64,
            u64, u64
        ),
        15 => register_source!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64,
            u64, u64, u64
        ),
        16 => register_source!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64,
            u64, u64, u64, u64
        ),
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
                    // log::debug!("name: {reactor_name}, inputs: {_inputs:?}");
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
        4 => register_sink!(dag, node_data, sched_type, u64, u64, u64, u64),
        5 => register_sink!(dag, node_data, sched_type, u64, u64, u64, u64, u64),
        6 => register_sink!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64),
        7 => register_sink!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64
        ),
        8 => register_sink!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64
        ),
        9 => {
            register_sink!(
                dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64
            )
        }
        10 => register_sink!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64
        ),
        11 => register_sink!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64
        ),
        12 => register_sink!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64
        ),
        13 => register_sink!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64,
            u64
        ),
        14 => register_sink!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64,
            u64, u64
        ),
        15 => register_sink!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64,
            u64, u64, u64
        ),
        16 => register_sink!(
            dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64,
            u64, u64, u64, u64
        ),
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
                    // log::debug!("name: {reactor_name}, inputs: {_inputs:?}, outputs: {outputs:?}");
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
        (1, 4) => register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64),
        (1, 5) => register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64, u64),
        (1, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64, u64, u64)
        }
        (1, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (1, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (1, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (1, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (1, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (1, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (1, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (1, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (1, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (1, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (2, 1) => register_intermediate!(dag, node_data, sched_type, u64, u64; u64),
        (2, 2) => register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64),
        (2, 3) => register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64),
        (2, 4) => register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64),
        (2, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64, u64)
        }
        (2, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (2, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (2, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (2, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (2, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (2, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (2, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (2, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (2, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (2, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (2, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (3, 1) => register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64),
        (3, 2) => register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64),
        (3, 3) => register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64),
        (3, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64)
        }
        (3, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (3, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (3, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (3, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (3, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (3, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (3, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (3, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (3, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (3, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (3, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (3, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (4, 1) => register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64),
        (4, 2) => register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64),
        (4, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64)
        }
        (4, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (4, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (4, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (4, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (4, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (4, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (4, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (4, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (4, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (4, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (4, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (4, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (4, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (5, 1) => register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64),
        (5, 2) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64)
        }
        (5, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64)
        }
        (5, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (5, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (5, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (5, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (5, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (5, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (5, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (5, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (5, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (5, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (5, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (5, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (5, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (6, 1) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64)
        }
        (6, 2) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64)
        }
        (6, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64)
        }
        (6, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (6, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (6, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (6, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (6, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (6, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (6, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (6, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (6, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (6, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (6, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (6, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (6, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (7, 1) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64)
        }
        (7, 2) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64)
        }
        (7, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64)
        }
        (7, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (7, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (7, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (7, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (7, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (7, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (7, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (7, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (7, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (7, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (7, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (7, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (7, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (8, 1) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64)
        }
        (8, 2) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64)
        }
        (8, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64)
        }
        (8, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (8, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (8, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (8, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (8, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (8, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (8, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (8, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (8, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (8, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (8, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (8, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (8, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (9, 1) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64)
        }
        (9, 2) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64)
        }
        (9, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64)
        }
        (9, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (9, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (9, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (9, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (9, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (9, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (9, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (9, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (9, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (9, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (9, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (9, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (9, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (10, 1) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64)
        }
        (10, 2) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64)
        }
        (10, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64)
        }
        (10, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (10, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (10, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (10, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (10, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (10, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (10, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (10, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (10, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (10, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (10, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (10, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (10, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (11, 1) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64)
        }
        (11, 2) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64)
        }
        (11, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64)
        }
        (11, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (11, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (11, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (11, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (11, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (11, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (11, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (11, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (11, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (11, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (11, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (11, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (11, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (12, 1) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64)
        }
        (12, 2) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64)
        }
        (12, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64)
        }
        (12, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (12, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (12, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (12, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (12, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (12, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (12, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (12, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (12, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (12, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (12, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (12, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (12, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (13, 1) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64)
        }
        (13, 2) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64)
        }
        (13, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64)
        }
        (13, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (13, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (13, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (13, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (13, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (13, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (13, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (13, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (13, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (13, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (13, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (13, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (13, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (14, 1) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64)
        }
        (14, 2) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64)
        }
        (14, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64)
        }
        (14, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (14, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (14, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (14, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (14, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (14, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (14, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (14, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (14, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (14, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (14, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (14, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (14, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (15, 1) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64)
        }
        (15, 2) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64)
        }
        (15, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64)
        }
        (15, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (15, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (15, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (15, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (15, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (15, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (15, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (15, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (15, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (15, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (15, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (15, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (15, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (16, 1) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64)
        }
        (16, 2) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64)
        }
        (16, 3) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64)
        }
        (16, 4) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64)
        }
        (16, 5) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64)
        }
        (16, 6) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64)
        }
        (16, 7) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64)
        }
        (16, 8) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (16, 9) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (16, 10) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (16, 11) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (16, 12) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (16, 13) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (16, 14) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (16, 15) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (16, 16) => {
            register_intermediate!(dag, node_data, sched_type, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64; u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64)
        }
        (i, o) if i > 16 && o > 16 => Err(LinkNumError::InOut(dag_id, node_id)),
        (i, _) if i > 16 => Err(LinkNumError::Input(dag_id, node_id)),
        (_, o) if o > 16 => Err(LinkNumError::Output(dag_id, node_id)),
        // Every (in, out) pair with both sides in 1..=16 is handled above; this
        // is a defensive fallback only, so a truly unexpected shape fails this
        // one DAG gracefully rather than panicking the whole kernel.
        _ => Err(LinkNumError::InOut(dag_id, node_id)),
    }
}

/// Builds `dag_data` into a registered `Dag`, or records why it failed (see
/// `awkernel_async_lib::dag::record_build_failure`) and returns the same
/// error as before. A DAG that fails here got a `dag_id` from `create_dag`
/// but never reaches `finish_create_dags`/spawn, so without this it would
/// never appear in the trace dump at all; recording it here means the host
/// sees a `TRACE_BUILD_MISS` line for it instead of it silently vanishing.
///
/// `federated_assignment` is this DAG's share of the Federated batch
/// decision (`federated::admit_batch`, made in `run()` over the whole task
/// set before any DAG is built); `None` on the `laxity`/`dagfluid` builds,
/// which decide per DAG inside `build_dag_impl`.
#[cfg(not(feature = "vfed"))]
pub(super) async fn build_dag(
    dag_data: DagData,
    federated_assignment: Option<FederatedAssignment>,
) -> Result<Arc<Dag>, BuildDagError> {
    match build_dag_impl(dag_data, federated_assignment).await {
        Ok(dag) => Ok(dag),
        Err((dag_id, e)) => {
            record_build_failure(dag_id, format!("{e}"));
            Err(e)
        }
    }
}

/// V-Fed's counterpart to `build_dag`, taking an `assignment` already
/// decided by a prior `vfed::admit_batch` call over the whole task set
/// (see `build_dag_impl_vfed`'s own doc).
#[cfg(feature = "vfed")]
pub(super) async fn build_dag_vfed(
    dag_data: DagData,
    assignment: vfed::VFedAssignment,
) -> Result<Arc<Dag>, BuildDagError> {
    match build_dag_impl_vfed(dag_data, assignment).await {
        Ok(dag) => Ok(dag),
        Err((dag_id, e)) => {
            record_build_failure(dag_id, format!("{e}"));
            Err(e)
        }
    }
}

/// Register every node of `dag_data` against `dag` under `sched_type`,
/// setting each node's laxity-derived priority too when `_node_laxity` is
/// `Some` (`laxity` feature only -- `None` on every other build, including
/// V-Fed's, which has no notion of node-level laxity). Shared tail of both
/// Federated/Laxity's per-DAG admission (`build_dag_impl`) and V-Fed's batch
/// admission (`build_dag_impl_vfed`), so this loop -- and its
/// `node.get_id()`-ordering assumption -- exists in exactly one place
/// regardless of which admission policy decided `sched_type`.
async fn register_dag_nodes(
    dag: &Arc<Dag>,
    dag_data: &DagData,
    sched_type: SchedulerType,
    _node_laxity: Option<BTreeMap<u32, u64>>,
) -> Result<(), BuildDagError> {
    for node in dag_data.get_nodes() {
        if node.is_source() {
            register_source_node(dag, node, sched_type).await?;
        } else if node.is_sink() {
            register_sink_node(dag, node, sched_type).await?;
        } else {
            register_intermediate_node(dag, node, sched_type).await?;
        }

        // Shorter laxity = more urgent: invert so it maps to a *larger*
        // `node_priority`, matching `gedf.rs`'s ordering
        // (`GEDFTask`'s `Ord` picks the *largest* `node_priority` first
        // among equal-deadline tasks). Called here, before
        // `finish_create_dags`, per `set_node_priority`'s own doc
        // requirement. `node.get_id()` is safe to use directly as the
        // runtime `node_id`: `DagData::get_nodes()` is backed by a
        // `BTreeMap<u32, NodeData>` keyed by this same id
        // (parse_yaml.rs's `convert_to_dag`), so registration happens in
        // ascending-id order and lines up with the sequential id
        // `register_*_reactor` assigns internally.
        #[cfg(feature = "laxity")]
        if let Some(laxity) = _node_laxity.as_ref().and_then(|m| m.get(&node.get_id())) {
            dag.set_node_priority(node.get_id(), u64::MAX.saturating_sub(*laxity));
        }
    }
    Ok(())
}

#[cfg(not(feature = "vfed"))]
async fn build_dag_impl(
    dag_data: DagData,
    _federated_assignment: Option<FederatedAssignment>,
) -> Result<Arc<Dag>, (u32, BuildDagError)> {
    let dag = create_dag();
    let dag_id = dag.get_id();

    let result: Result<Arc<Dag>, BuildDagError> = async {
    let stats = compute_dag_stats(&dag_data);
    log::debug!(
        "DAG#{dag_id}: volume(C)={}, critical_path(L)={}",
        stats.volume,
        stats.critical_path
    );

    let period = dag_data
        .get_nodes()
        .iter()
        .find(|node| node.is_source())
        .and_then(NodeData::get_period)
        .ok_or(DagError::MissingTiming(dag_id))?;
    let relative_deadline = dag_data
        .get_nodes()
        .iter()
        .find(|node| node.is_sink())
        .and_then(NodeData::get_end_to_end_deadline)
        .ok_or(DagError::MissingTiming(dag_id))?;

    // Laxity/DAG-Fluid admit one DAG at a time here, so their preconditions
    // are checked here, against this DAG's own id, before any admission
    // work (Federated/V-Fed check theirs in their batch admission in
    // `run()`).
    #[cfg(any(feature = "laxity", feature = "dagfluid"))]
    let config = DagMetrics::from_static(stats.volume, stats.critical_path, period, relative_deadline);
    #[cfg(feature = "laxity")]
    precondition::check(Policy::Laxity, dag_id, &config)?;
    #[cfg(feature = "dagfluid")]
    precondition::check(Policy::DagFluid, dag_id, &config)?;
    // Federated already read both from the same nodes in `run()`'s batch
    // admission; they are still fetched above so a DAG missing either is
    // rejected with the same `DagError::MissingTiming` error on every build.
    #[cfg(not(any(feature = "laxity", feature = "dagfluid")))]
    let _ = (period, relative_deadline);

    // Federated: the decision was already made for the whole task set by
    // `federated::admit_batch` in `run()` (the papers' algorithms are
    // batch algorithms -- high-density DAGs first, then partitioning of the
    // rest -- so admitting DAGs one at a time in file order would not be
    // the same algorithm); this only reads that decision back.
    #[cfg(not(any(feature = "laxity", feature = "dagfluid")))]
    let sched_type = {
        let assignment =
            _federated_assignment.ok_or(BuildDagError::FederatedNotAdmitted(dag_id))?;
        let sched_type = assignment.scheduler_type;
        if let SchedulerType::ClusteredEDF(deadline, cluster) = sched_type {
            let cores: Vec<usize> = cluster.iter().collect();
            log::info!(
                "DAG#{dag_id}: admitted (federated) as {:?} ({:?}) -> ClusteredEDF(relative_deadline={deadline}, cores={cores:?})",
                assignment.class,
                assignment.source
            );
        } else {
            log::info!(
                "DAG#{dag_id}: admitted (federated) as {:?} ({:?}) -> {sched_type:?}",
                assignment.class,
                assignment.source
            );
        }
        sched_type
    };

    // "Static Laxity-Based" baseline: plain (non-clustered) GEDF, with a
    // per-node priority tie-break computed offline from `compute_node_laxity`
    // (shorter laxity = more urgent = higher priority, per `dag.rs`/
    // `gedf.rs`/`clustered_edf.rs`'s shared "higher `node_priority` picked
    // first" convention). This baseline has no published primary source of
    // its own -- see `compute_node_laxity`'s own doc for why -- it exists as
    // a self-derived structural counterpart to He et al. 2019 for
    // comparison purposes, not a reproduction of any specific paper.
    #[cfg(feature = "laxity")]
    let (sched_type, node_laxity) = {
        let laxity =
            // `None` only for `D <= L`, which the precondition above rejects.
            compute_node_laxity(&dag_data, relative_deadline).ok_or(DagError::NonPositiveSlack {
                dag_id,
                critical_path: stats.critical_path,
                relative_deadline,
            })?;
        let sched_type = SchedulerType::GEDF(relative_deadline);
        log::info!(
            "DAG#{dag_id}: admitted (laxity) {config:?} -> {sched_type:?}, node_laxity={laxity:?}"
        );
        (sched_type, laxity)
    };

    // DAG-Fluid (see `awkernel_async_lib::dag_sched::policy::dag_fluid`'s own doc): `required_capacity`
    // gives this DAG's own real-valued contribution to the shared capacity
    // pool -- order-independent (unlike V-Fed's Algorithm 1,
    // `Σrequired_capacity_i <= m` is a plain running sum), so admitting one
    // DAG at a time in file order, same as Federated/Laxity above, is
    // exactly equivalent to a batch run; no `admit_batch`-style two-pass
    // dance is needed here.
    //
    // Resource model: every DAG-Fluid DAG shares one pool of cores
    // (`resource::reserve_dagfluid_capacity`/`dagfluid_pool_cpu_set`) --
    // fluid theory's own assumption (`Σrequired_capacity_i <= m`), matching
    // the same aggregate check `dag_fluid::is_batch_feasible` already runs
    // offline -- rather than each DAG claiming an exclusive cluster the way
    // an earlier revision of this arm did (Federated/V-Fed-style, one
    // cluster per DAG; superseded because it can't express multiple
    // DAG-Fluid tasks actually sharing capacity).
    //
    // Dispatch: still a *placeholder*, not the papers' DP-Fair/DP-Wrap
    // fluid-rate execution -- plain `GEDF` over the shared pool (the same
    // placeholder role Federated's light tasks already use `GEDF` for).
    // The real DP-Wrap dispatch mechanism (Funk, Levin, Sadowski, Pye,
    // Brandt, "DP-Fair: A unifying theory for optimal hard real-time
    // multiprocessor scheduling", Real-Time Systems 2011) is not
    // implemented yet -- deliberately deferred pending that paper's own
    // primary source (not just the DAG-Fluid paper's summary of it) so its
    // 3 dispatch rules (Section 8) are transcribed precisely rather than
    // reconstructed from a secondary description. See this crate's own
    // `dag_fluid.rs` module doc.
    #[cfg(feature = "dagfluid")]
    let sched_type = {
        let graph = crate::dag_graph(&dag_data).map_err(|e| {
            log::warn!("DAG#{dag_id}: cannot build its graph for DAG-Fluid: {e}");
            AdmissionError::NoFeasibleAllocation
        })?;
        let segments = awkernel_async_lib::dag_sched::policy::dag_fluid::decompose_segments(&graph);
        let required = awkernel_async_lib::dag_sched::policy::dag_fluid::required_capacity(
            stats.volume,
            period,
            stats.critical_path,
            relative_deadline,
            &segments,
        )
        // `L > D` was rejected by the precondition above, so `None` here is
        // a degenerate segment decomposition (see `required_capacity`).
        .ok_or(AdmissionError::NoFeasibleAllocation)?;
        resource::reserve_dagfluid_capacity(required)?;

        // Real dispatch (`scheduler::dp_wrap` / `dag_sched::dp_partition`):
        // compute the Section 8 Step 1 thread-list conversion (Algorithm 1
        // lines 16-21, see `dag_fluid::assign_segment_deadlines`'s own
        // doc) and this task's own completion gates
        // (`dag_fluid::segment_completion_gates`), and register each
        // segment with the system-wide DP-boundary tracker. Only
        // meaningful for a task actually decomposed into segments
        // (`stats.volume > d_star`, i.e. the `τ_paral` case, Section 4.1)
        // -- a `τ_seq` task (whole DAG stretched into one sequential unit)
        // has no segments to convert or register, and keeps the plain
        // `GEDF` placeholder dispatch DAG-Fluid's static-only Phase 0 used
        // (see `SchedulerType::GEDF`'s own doc: fine for a task DP-Wrap
        // would reduce to trivially anyway with no segment boundaries to
        // track).
        let d_star = awkernel_async_lib::dag_sched::policy::dag_fluid::virtual_deadline(period, relative_deadline, stats.critical_path);
        let schedule = if stats.volume > d_star {
            awkernel_async_lib::dag_sched::policy::dag_fluid::assign_segment_deadlines(&segments, stats.volume, d_star)
        } else {
            None
        };

        let sched_type = if schedule.is_some() {
            SchedulerType::DpWrap(dag_id)
        } else {
            SchedulerType::GEDF(relative_deadline)
        };
        log::info!(
            "DAG#{dag_id}: admitted (dagfluid, shared pool) required_capacity={required:.3} -> {sched_type:?}"
        );

        if let Some(schedule) = schedule {
            let offsets = awkernel_async_lib::dag_sched::policy::dag_fluid::segment_release_offsets(&schedule);
            // Gates come back as graph indices; `dp_partition` watches node ids.
            let node_ids = crate::sorted_node_ids(&dag_data);
            let gates: Vec<Vec<u32>> =
                awkernel_async_lib::dag_sched::policy::dag_fluid::segment_completion_gates(&graph)
                    .into_iter()
                    .map(|gate| gate.iter().filter_map(|&v| node_ids.get(v).copied()).collect())
                    .collect();
            // All of this DAG's own segments share one release-time
            // baseline (see `dp_partition`'s own doc on why
            // `Instant::now()` at admission stands in for the papers'
            // `r_i,j` anchor here).
            let release = awkernel_lib::time::Instant::now();
            for (j, (seg, offset)) in schedule.iter().zip(offsets.iter()).enumerate() {
                log::info!(
                    "DAG#{dag_id}: segment[{j}] l={} m={} r={offset:.3} d={:.3} theta={:.3}",
                    seg.duration,
                    seg.concurrency,
                    seg.relative_deadline,
                    seg.rate
                );
                let gate = gates.get(j).cloned().unwrap_or_default();
                awkernel_async_lib::dag_sched::dp_partition::register_segment(
                    dag_id,
                    j,
                    release,
                    *offset,
                    seg.relative_deadline,
                    seg.concurrency,
                    seg.rate,
                    gate,
                );
            }
        }
        sched_type
    };

    #[cfg(feature = "laxity")]
    register_dag_nodes(&dag, &dag_data, sched_type, Some(node_laxity)).await?;
    #[cfg(not(feature = "laxity"))]
    register_dag_nodes(&dag, &dag_data, sched_type, None).await?;

    Ok(dag)
    }
    .await;

    result.map_err(|e| (dag_id, e))
}

/// V-Fed's batch counterpart to `build_dag_impl`: `assignment` was already
/// decided for the *whole* task set by `vfed::admit_batch` (see that
/// function's own doc, and `dag_sched::policy::vfed`'s module doc for why
/// V-Fed needs this instead of one `admit_one` call per DAG -- Algorithm 1
/// sorts and packs the entire batch together, so admitting DAGs one at a
/// time in file order isn't equivalent). This function only turns that
/// pre-decided `assignment` into node registrations; it does no admission
/// of its own.
#[cfg(feature = "vfed")]
async fn build_dag_impl_vfed(
    dag_data: DagData,
    assignment: vfed::VFedAssignment,
) -> Result<Arc<Dag>, (u32, BuildDagError)> {
    let dag = create_dag();
    let dag_id = dag.get_id();

    let result: Result<Arc<Dag>, BuildDagError> = async {
        let stats = compute_dag_stats(&dag_data);
        log::debug!(
            "DAG#{dag_id}: volume(C)={}, critical_path(L)={}",
            stats.volume,
            stats.critical_path
        );

        let relative_deadline = dag_data
            .get_nodes()
            .iter()
            .find(|node| node.is_sink())
            .and_then(NodeData::get_end_to_end_deadline)
            .ok_or(DagError::MissingTiming(dag_id))?;

        let sched_type = assignment
            .into_scheduler_type(relative_deadline)
            .ok_or(BuildDagError::VFedSchedulerTypeMissing(dag_id))?;
        log::info!("DAG#{dag_id}: admitted (vfed, batch) as {assignment:?} -> {sched_type:?}");

        register_dag_nodes(&dag, &dag_data, sched_type, None).await?;

        Ok(dag)
    }
    .await;

    result.map_err(|e| (dag_id, e))
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
