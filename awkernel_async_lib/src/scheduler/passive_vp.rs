//! V-Fed's passive-VP scheduler ([`crate::dag_sched::policy::vfed`]): the
//! complementary, low-priority half of [`super::active_vp`] — a task
//! assigned to one or more *other* DAGs' leftover active-VP capacity
//! (Theorem 2/4's passive-VPs).
//!
//! Structurally almost identical to [`super::clustered_edf`] (same
//! cpu_set-restricted affinity queue, same `invoke_preemption` pattern,
//! copied rather than shared because it is a separate, independently
//! reasoned-about priority tier — see `crate::scheduler::SchedulerType`'s
//! doc on `PRIORITY_LIST` ordering). The one addition: [`get_next`] yields
//! (returns `None` without even touching the queue) whenever the cpu's
//! active-VP owner is currently executing there. This is the exact
//! "unavailable if the active-VP on that processor is executing" rule the
//! papers' passive-VP definition uses; it is checked, not assumed, by
//! reading `task::RUNNING` (via `get_task_running`) and the running task's
//! own `SchedulerType` — both already-authoritative, always-current state
//! the executor itself maintains, so this adds no new bookkeeping and
//! cannot drift out of sync with it.
//!
//! A passive-VP task can never need to preempt the active-VP owner: since
//! `PriorityInfo` packs `(scheduler_class_priority, task_priority)` and
//! `ActiveVp` sits above `PassiveVp` in `PRIORITY_LIST`, the generic
//! `task > target_task` comparison [`PassiveVpScheduler::invoke_preemption`]
//! reuses from `ClusteredEDF` is *never* true when `target_task` is the
//! active-VP owner — no special case needed, the packed comparison already
//! rules it out.
//!
//! # WCET contract ([`active_vp_is_busy`])
//! - No heap allocation, no blocking, no `.await`.
//! - O(1): one atomic load (`get_task_running`) plus one bounded lookup
//!   (`get_scheduler_type_by_task_id`, itself a `BTreeMap` lookup bounded
//!   by the live task count) and one info-lock acquisition — the same cost
//!   `ClusteredEDF`/`GEDF`'s existing `invoke_preemption` already pays per
//!   candidate cpu, not a new class of expense.
//! - Never panics.

use super::{
    get_priority, peek_preemption_pending, push_preemption_pending, ClusteredTask, Scheduler,
    SchedulerType, Task, GLOBAL_WAKE_GET_MUTEX, PREEMPTION_ENABLED,
};
use crate::{
    dag::calculate_and_update_dag_deadline,
    task::{
        get_scheduler_type_by_task_id, get_task, get_task_running, set_current_task,
        set_need_preemption, State, MAX_TASK_PRIORITY,
    },
};
use affinity_btree_queue::{AffinityBTreeQueue, DEFAULT_MIN_DEGREE};
use alloc::sync::Arc;
use awkernel_lib::{
    cpu::{masked_workers, num_cpu, CpuSet, CPU_SET_WORDS},
    sync::mutex::{MCSNode, Mutex},
};

/// True if `cpu`'s active-VP owner is currently executing something there
/// right now — the exact condition the papers key passive-VP
/// availability on. `false` (available to passive-VP work) both when the
/// cpu is genuinely idle and when whatever is running there is not an
/// active-VP task at all (e.g. this same passive-VP task already running).
///
/// A pure [`SchedulerType::ActiveVp`] task running on `cpu_id` is always
/// its own group's owner. A [`SchedulerType::MixedVp`] task counts too, but
/// *only* while `cpu_id` is one of its own `active_set` cores — the same
/// task could equally be running on `cpu_id` as a *borrower* of some other
/// DAG's passive-VP (its own `passive_set`), which must not read as "the
/// owner is busy" here (that would be asking whether `cpu_id`'s owner is
/// busy running some *other* DAG's borrowed execution, a category error).
/// Shared by [`PassiveVpScheduler::get_next`] and
/// [`super::mixed_vp::MixedVpScheduler::get_next`]'s own borrowed-core
/// branch.
pub(crate) fn active_vp_is_busy(cpu_id: usize) -> bool {
    let running = get_task_running(cpu_id);
    if running.task_id == 0 {
        return false;
    }
    match get_scheduler_type_by_task_id(running.task_id) {
        Some(SchedulerType::ActiveVp(_, _)) => true,
        Some(SchedulerType::MixedVp(active_set, _, _)) => active_set.contains(cpu_id),
        _ => false,
    }
}

/// Same key/ordering as `ClusteredEDF`/`ActiveVp` (see those modules):
/// reused verbatim rather than redesigned, since nothing about the
/// passive-VP role changes what a reasonable dispatch order looks like.
type PassiveVpQueue = AffinityBTreeQueue<
    (u64, u64, u64),
    ClusteredTask<Arc<Task>>,
    DEFAULT_MIN_DEGREE,
    CPU_SET_WORDS,
>;

pub struct PassiveVpScheduler {
    data: Mutex<Option<PassiveVpQueue>>,
    priority: u8,
}

impl Scheduler for PassiveVpScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let (wake_time, absolute_deadline, node_priority, cpu_set) = {
            let mut node_inner = MCSNode::new();
            let mut info = task.info.lock(&mut node_inner);
            let dag_info = info.get_dag_info();
            match info.scheduler_type {
                SchedulerType::PassiveVp(cpu_set) => {
                    let wake_time = awkernel_lib::delay::uptime();
                    let (absolute_deadline, node_priority) = if let Some(ref dag_info) = dag_info {
                        (
                            calculate_and_update_dag_deadline(dag_info, wake_time, info.state),
                            crate::dag::get_node_priority(dag_info.dag_id, dag_info.node_id),
                        )
                    } else {
                        (wake_time, 0)
                    };

                    task.priority
                        .update_priority_info(self.priority, MAX_TASK_PRIORITY - absolute_deadline);
                    info.update_absolute_deadline(absolute_deadline);

                    (wake_time, absolute_deadline, node_priority, cpu_set)
                }
                _ => unreachable!(),
            }
        };

        if cpu_set.is_empty() || masked_workers(cpu_set, num_cpu()) != cpu_set {
            unreachable!("PassiveVp: cpu_set {cpu_set:?} was not normalized by spawn");
        }

        let mut node = MCSNode::new();
        let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);
        if !self.invoke_preemption(task.clone()) {
            let mut node_inner = MCSNode::new();
            let mut data = self.data.lock(&mut node_inner);
            let queue = data.get_or_insert_with(|| PassiveVpQueue::new(num_cpu()));
            let _ = queue.push(
                (absolute_deadline, u64::MAX - node_priority, wake_time),
                cpu_set,
                ClusteredTask::new(task.clone()),
            );
        }
    }

    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>> {
        let cpu_id = awkernel_lib::cpu::cpu_id();
        if active_vp_is_busy(cpu_id) {
            return None;
        }

        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);
        let queue = (*data).as_mut()?;

        loop {
            let (_, _, mut entry) = queue.pop_for_cpu(cpu_id)?;
            let Some(task) = entry.take() else {
                continue;
            };

            {
                let mut node = MCSNode::new();
                let mut task_info = task.info.lock(&mut node);

                if matches!(task_info.state, State::Terminated | State::Panicked) {
                    continue;
                }
                if task_info.state == State::Preempted {
                    task_info.need_preemption = false;
                }
                if execution_ensured {
                    task_info.state = State::Running;
                    set_current_task(cpu_id, task.id);
                }
            }

            return Some(task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::PassiveVp(CpuSet::empty())
    }

    fn priority(&self) -> u8 {
        self.priority
    }

    fn queued_cpu_mask(&self) -> CpuSet {
        let mut node = MCSNode::new();
        let data = self.data.lock(&mut node);
        match &*data {
            Some(queue) => queue.affinity_mask(),
            None => CpuSet::empty(),
        }
    }
}

pub static SCHEDULER: PassiveVpScheduler = PassiveVpScheduler {
    data: Mutex::new(None),
    priority: get_priority(&SchedulerType::PassiveVp(CpuSet::empty())),
};

impl PassiveVpScheduler {
    /// Identical in structure to `ClusteredEDFScheduler::invoke_preemption`
    /// (see that module and this module's doc for why it is safe to reuse
    /// verbatim: the packed `PriorityInfo` comparison already prevents this
    /// from ever displacing an active-VP owner).
    fn invoke_preemption(&self, task: Arc<Task>) -> bool {
        if !PREEMPTION_ENABLED {
            return false;
        }

        let cpu_set = task.cpu_set.expect("Task has no CPU set");

        let mut victim: Option<(usize, Arc<Task>)> = None;

        for cpu_id in cpu_set.iter() {
            let task_running = get_task_running(cpu_id);

            if task_running.task_id == task.id {
                return false;
            }
            if task_running.task_id == 0 {
                return false;
            }

            let task_running = get_task(task_running.task_id);
            let task_pending = peek_preemption_pending(cpu_id);

            let target_task = match (task_running, task_pending) {
                (Some(running), Some(pending)) => running.max(pending),
                (Some(running), None) => running,
                (None, Some(pending)) => pending,
                (None, None) => return false,
            };

            match victim {
                Some((_, ref lowest)) if target_task >= *lowest => (),
                _ => victim = Some((cpu_id, target_task)),
            }
        }

        let Some((victim_cpu, target_task)) = victim else {
            return false;
        };

        if task > target_task {
            push_preemption_pending(victim_cpu, task);
            let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
            set_need_preemption(target_task.id, victim_cpu);
            awkernel_lib::interrupt::send_ipi(preempt_irq, victim_cpu as u32);
            return true;
        }

        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_active_vp_is_busy_false_when_idle() {
        // cpu 0 is never assigned a running task in this test process.
        assert!(!active_vp_is_busy(0));
    }
}
