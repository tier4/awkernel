//! Earliest Deadline First, ordered by the real job deadline.

use super::{
    clustered::{ClusteredOrdering, ClusteredScheduler},
    SchedulerType,
};
use crate::{dag::calculate_and_update_dag_deadline, task::TaskInfo};
use awkernel_lib::cpu::CpuSet;

pub(super) struct Edf;

pub(super) static SCHEDULER: ClusteredScheduler<Edf> = ClusteredScheduler::new();

impl ClusteredOrdering for Edf {
    const KIND: SchedulerType = SchedulerType::EDF(0, CpuSet::empty());

    fn ready_priority(info: &TaskInfo, wake_time: u64) -> (u64, u64) {
        let SchedulerType::EDF(relative_deadline, _) = info.scheduler_type else {
            unreachable!("non-EDF task routed to EDF");
        };
        let deadline = match &info.dag_info {
            Some(dag_info) => calculate_and_update_dag_deadline(dag_info, wake_time, info.state),
            None => wake_time + relative_deadline,
        };
        (deadline, deadline)
    }
}
