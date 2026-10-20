//! A GEDF scheduler.
//!
//! Every node of a DAG job gets the deadline `release time + sink relative deadline`.

use super::{
    dag_edf::{calculate_dag_deadline, DagEdfPolicy, DagEdfScheduler},
    SchedulerType,
};
use crate::{
    dag::{Dag, NodeIndex},
    task::{DagInfo, State},
};

pub struct GedfPolicy;

pub type GEDFScheduler = DagEdfScheduler<GedfPolicy>;

pub static SCHEDULER: GEDFScheduler = DagEdfScheduler::new();

impl DagEdfPolicy for GedfPolicy {
    const SCHEDULER_TYPE: SchedulerType = SchedulerType::GEDF(0);
    const NAME: &'static str = "GEDF";

    fn relative_deadline(scheduler_type: &SchedulerType) -> Option<u64> {
        match scheduler_type {
            SchedulerType::GEDF(relative_deadline) => Some(*relative_deadline),
            _ => None,
        }
    }

    fn dag_deadline(dag: &Dag, node_idx: NodeIndex, release: bool, wake_time: u64) -> u64 {
        let (release_time, _) = dag.get_or_release_job(node_idx, release, || wake_time, |_| ());
        let sink_deadline_us = dag
            .get_sink_relative_deadline()
            .map(|deadline| deadline.as_micros() as u64)
            .unwrap_or_else(|_| panic!("GEDF scheduler: DAG has no sink relative deadline set"));
        release_time.saturating_add(sink_deadline_us)
    }
}

/// Returns the absolute deadline of the DAG job that the node of `dag_info` processes next,
/// with the GEDF rule.
///
/// # Panics
///
/// Panics if the DAG does not exist or has no sink relative deadline.
pub fn calculate_and_update_dag_deadline(dag_info: &DagInfo, wake_time: u64, state: State) -> u64 {
    calculate_dag_deadline::<GedfPolicy>(dag_info, wake_time, state)
}
