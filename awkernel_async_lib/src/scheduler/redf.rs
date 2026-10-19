//! A REDF (Relative Earliest Deadline First) scheduler.
//!
//! Each node of a DAG job gets its own deadline: `release time + node relative deadline`.
//! The relative deadline of a node is its latest finish time, computed from the sink deadline
//! and the estimated WCETs when the DAG is built.

use super::{
    dag_edf::{DagEdfPolicy, DagEdfScheduler},
    SchedulerType,
};
use crate::dag::{Dag, NodeIndex};

pub struct RedfPolicy;

pub type REDFScheduler = DagEdfScheduler<RedfPolicy>;

pub static SCHEDULER: REDFScheduler = DagEdfScheduler::new();

impl DagEdfPolicy for RedfPolicy {
    const SCHEDULER_TYPE: SchedulerType = SchedulerType::REDF(0);
    const NAME: &'static str = "REDF";

    fn relative_deadline(scheduler_type: &SchedulerType) -> Option<u64> {
        match scheduler_type {
            SchedulerType::REDF(relative_deadline) => Some(*relative_deadline),
            _ => None,
        }
    }
    // REDF uses per-node relative deadlines
    fn dag_deadline(dag: &Dag, node_idx: NodeIndex, release: bool, wake_time: u64) -> u64 {
        dag.get_or_release_absolute_deadline(node_idx, release, || wake_time)
    }
}
