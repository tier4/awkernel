//! Least Latest Finish Time (LLFT) scheduler, prioritizing tasks by their latest finish time.

use super::{
    clustered::{ClusteredOrdering, ClusteredScheduler},
    SchedulerType,
};
use crate::{dag::calculate_dag_latest_finish_priority, task::TaskInfo};
use awkernel_lib::cpu::CpuSet;

pub(super) struct LeastLatestFinish;

pub(super) static SCHEDULER: ClusteredScheduler<LeastLatestFinish> = ClusteredScheduler::new();

impl ClusteredOrdering for LeastLatestFinish {
    const KIND: SchedulerType = SchedulerType::LLFT(0, CpuSet::empty());

    fn ready_priority(info: &TaskInfo, wake_time: u64) -> (u64, u64) {
        let SchedulerType::LLFT(relative_deadline, _) = info.scheduler_type else {
            unreachable!("non-LLFT task routed to LLFT");
        };
        match &info.dag_info {
            Some(dag_info) => calculate_dag_latest_finish_priority(dag_info, wake_time, info.state),
            None => {
                let deadline = wake_time + relative_deadline;
                (deadline, deadline)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scheduler::get_priority;

    #[test]
    fn clustered_policy_is_distinct_and_below_edf() {
        let edf = SchedulerType::EDF(10, CpuSet::all());
        let latest = SchedulerType::LLFT(10, CpuSet::all());
        assert!(!latest.equals(&edf));
        assert!(latest.equals(&SchedulerType::LLFT(20, CpuSet::empty())));
        assert!(latest.is_clustered());
        assert_eq!(latest.cpu_set(), Some(CpuSet::all()));
        assert!(get_priority(&edf) > get_priority(&latest));
        assert!(get_priority(&latest) > get_priority(&SchedulerType::PrioritizedFIFO(0)));
    }
}
