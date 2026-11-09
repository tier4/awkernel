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

    // REDF uses the estimated latest finish of each node.
    fn dag_deadline(dag: &Dag, node_idx: NodeIndex, release: bool, wake_time: u64) -> u64 {
        let (release_time, latest_finish) = dag.get_or_release_job(
            node_idx,
            release,
            || wake_time,
            |timing| timing.estimated_latest_finish.as_micros() as u64,
        );
        release_time.saturating_add(latest_finish)
    }
}
