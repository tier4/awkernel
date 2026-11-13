//! A GEDF scheduler.

use super::{
    dag_edf::{calculate_dag_deadline, DagEdfPolicy, DagEdfScheduler},
    SchedulerType,
};
use crate::{
    dag::{to_node_index, Dag},
    task::{DagInfo, State},
};

pub struct GedfPolicy;

pub type GEDFScheduler = DagEdfScheduler<GedfPolicy>;

pub static SCHEDULER: GEDFScheduler = GEDFScheduler::new();

impl DagEdfPolicy for GedfPolicy {
    const SCHEDULER_TYPE: SchedulerType = SchedulerType::GEDF(0);
    const NAME: &'static str = "GEDF";

    fn relative_deadline(scheduler_type: &SchedulerType) -> Option<u64> {
        match scheduler_type {
            SchedulerType::GEDF(relative_deadline) => Some(*relative_deadline),
            _ => None,
        }
    }

    fn dag_deadline(dag: &Dag, node_id: u32, release: bool, wake_time: u64) -> u64 {
        dag.get_or_release_job(to_node_index(node_id), release)
            .map_or_else(
                || {
                    // Microseconds, the unit of `awkernel_lib::delay::uptime()`.
                    let relative_deadline_us = dag
                        .get_sink_relative_deadline()
                        .map(|deadline| deadline.as_micros() as u64)
                        .unwrap_or_else(|_| {
                            let dag_id = dag.get_id();
                            panic!("GEDF scheduler: DAG {dag_id} has no sink relative deadline set")
                        });
                    wake_time + relative_deadline_us
                },
                |job| job.absolute_deadline,
            )
    }
}

/// Returns the absolute deadline of the DAG job that the node of `dag_info` processes next.
/// A source wake in any `state` except `State::Preempted` releases an unreleased job. Its
/// absolute deadline is fixed at release to the interval tick target plus the sink relative
/// deadline. A wake before release gets `wake_time` plus the current sink relative deadline.
///
/// # Panics
///
/// Panics if the DAG does not exist, has no node `dag_info.node_id`, or has no sink relative
/// deadline, or the source releases a job without an interval tick target.
pub fn calculate_and_update_dag_deadline(dag_info: &DagInfo, wake_time: u64, state: State) -> u64 {
    calculate_dag_deadline::<GedfPolicy>(dag_info, wake_time, state)
}
