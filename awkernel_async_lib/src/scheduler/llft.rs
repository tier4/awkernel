//! Least latest finish　time first, distinct from the real job deadline.

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
    use affinity_btree_queue::{AffinityBTreeQueue, DEFAULT_MIN_DEGREE};
    use awkernel_lib::cpu::CPU_SET_WORDS;

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

    #[test]
    fn affinity_queue_orders_latest_finish_then_wake_time() {
        let mut queue =
            AffinityBTreeQueue::<(u64, u64), &str, DEFAULT_MIN_DEGREE, CPU_SET_WORDS>::new(3);
        let worker_one = CpuSet::empty().with(1);
        let worker_two = CpuSet::empty().with(2);
        queue.push((50, 20), worker_one, "later wake").unwrap();
        queue.push((70, 5), worker_one, "later finish").unwrap();
        queue.push((50, 10), worker_one, "earlier wake").unwrap();
        queue.push((40, 1), worker_two, "other CPU").unwrap();

        assert_eq!(queue.pop_for_cpu(1).unwrap().2, "earlier wake");
        assert_eq!(queue.pop_for_cpu(1).unwrap().2, "later wake");
        assert_eq!(queue.pop_for_cpu(1).unwrap().2, "later finish");
        assert_eq!(queue.pop_for_cpu(2).unwrap().2, "other CPU");
    }
}
