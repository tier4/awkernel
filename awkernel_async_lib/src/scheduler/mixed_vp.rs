//! V-Fed's mixed active+passive scheduler ([`crate::dag_sched::policy::vfed`],
//! Theorem 4): a heavy DAG whose active-VP group came up short on free
//! cores, topped up with *other* DAGs' leftover passive-VPs. A single task
//! registered with [`crate::scheduler::SchedulerType::MixedVp`] must
//! therefore be dispatchable on **both** its own budget/leading-gated
//! `active_set` cores (exactly [`super::active_vp`]'s rules) **and** its
//! borrowed `passive_set` cores (exactly [`super::passive_vp`]'s rule:
//! available only while that core's own active-VP owner isn't executing
//! there) — whichever becomes eligible first, work-conserving across both.
//!
//! # Why one queue, not two
//!
//! A DAG's ready nodes are individually spawned tasks; at any moment there
//! may be more of them ready than this group's `active_set` alone can run,
//! which is exactly when the `passive_set` top-up matters. A given node
//! must be claimable from *either* set but **only once** — pushing the same
//! wake into two separate scheduler queues (one restricted to `active_set`,
//! one to `passive_set`) would let two different cpus both pop it (nothing
//! links the two entries together). Instead this module pushes **one**
//! queue entry per wake, with `affinity = active_set ∪ passive_set`:
//! [`affinity_btree_queue::AffinityBTreeQueue`] already guarantees an entry
//! is popped by at most one cpu among its affinity set — the same primitive
//! `ClusteredEDF`'s own multi-core clusters already rely on — so no new
//! claim/invalidate bookkeeping is needed for that part.
//!
//! What *is* new: which gate applies depends on which side of the union
//! `cpu_id` falls on for the *specific* entry being considered, and that is
//! only knowable once it's popped (querying the popped task's own
//! `SchedulerType::MixedVp`). [`MixedVpScheduler::get_next`] therefore pops
//! candidates in priority order, defers (holds aside, not discarded) any
//! whose applicable gate isn't satisfied yet, and re-pushes every deferred
//! entry before returning — so a higher-priority but momentarily-ineligible
//! entry (e.g. this group's own vertex with its active-side budget
//! currently exhausted) can never block a lower-priority but
//! currently-eligible one (e.g. a different vertex eligible on a borrowed
//! core) from being found. Bounded by the number of currently-queued
//! entries actually reachable from `cpu_id`, the same bound the
//! Terminated/Panicked-skipping loop every clustered scheduler already has.
//!
//! # WCET
//! No longer O(1) like the pure schedulers' pop path (the defer/re-push
//! loop can visit more than one entry), but bounded by the live queue depth
//! for `cpu_id` — the same class of bound already accepted for the
//! terminated/panicked-skipping loop shared by every clustered scheduler in
//! this codebase.

use super::{
    active_vp, get_priority, passive_vp, peek_preemption_pending, push_preemption_pending,
    ClusteredTask, Scheduler, SchedulerType, Task, GLOBAL_WAKE_GET_MUTEX, PREEMPTION_ENABLED,
};
use crate::{
    dag::{calculate_and_update_dag_deadline, is_job_release_wake},
    task::{
        get_task, get_task_running, set_current_task, set_need_preemption, State, MAX_TASK_PRIORITY,
    },
};
use affinity_btree_queue::{AffinityBTreeQueue, DEFAULT_MIN_DEGREE};
use alloc::{sync::Arc, vec::Vec};
use awkernel_lib::{
    cpu::{masked_workers, num_cpu, CpuSet, CPU_SET_WORDS},
    sync::mutex::{MCSNode, Mutex},
};

type MixedVpQueue = AffinityBTreeQueue<
    (u64, u64, u64),
    ClusteredTask<Arc<Task>>,
    DEFAULT_MIN_DEGREE,
    CPU_SET_WORDS,
>;

/// A popped queue entry held aside by `get_next`: `(key, cpu_set, task)`.
type DeferredEntry = ((u64, u64, u64), CpuSet, ClusteredTask<Arc<Task>>);

pub struct MixedVpScheduler {
    data: Mutex<Option<MixedVpQueue>>,
    priority: u8,
}

impl Scheduler for MixedVpScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let (wake_time, absolute_deadline, node_priority, active_set, leading_cpu, cpu_set) = {
            let mut node_inner = MCSNode::new();
            let mut info = task.info.lock(&mut node_inner);
            let dag_info = info.get_dag_info();
            match info.scheduler_type {
                SchedulerType::MixedVp(active_set, leading_cpu, passive_set) => {
                    let wake_time = awkernel_lib::delay::uptime();
                    let (absolute_deadline, node_priority) = if let Some(ref dag_info) = dag_info {
                        if is_job_release_wake(dag_info, info.state) {
                            // Only this group's own cores replenish here —
                            // the borrowed `passive_set` cores' budgets (if
                            // any) belong to whichever *other* DAG owns
                            // them, replenished by that DAG's own wake.
                            active_vp::replenish(active_set);
                        }
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

                    let cpu_set = active_set.union(passive_set);
                    (
                        wake_time,
                        absolute_deadline,
                        node_priority,
                        active_set,
                        leading_cpu,
                        cpu_set,
                    )
                }
                _ => unreachable!(),
            }
        };

        if cpu_set.is_empty() || masked_workers(cpu_set, num_cpu()) != cpu_set {
            unreachable!("MixedVp: cpu_set {cpu_set:?} was not normalized by spawn");
        }

        // Only this group's own active cores get a leading-core record here
        // — a borrowed passive core's leading core belongs to a *different*
        // DAG's active-VP group and must be left exactly as that DAG's own
        // `wake_task` set it.
        for cpu in active_set.iter() {
            active_vp::set_leading(cpu, leading_cpu);
        }

        let mut node = MCSNode::new();
        let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);

        if !self.invoke_preemption(task.clone()) {
            let mut node_inner = MCSNode::new();
            let mut data = self.data.lock(&mut node_inner);
            let queue = data.get_or_insert_with(|| MixedVpQueue::new(num_cpu()));
            let _ = queue.push(
                (absolute_deadline, u64::MAX - node_priority, wake_time),
                cpu_set,
                ClusteredTask::new(task.clone()),
            );
        }
    }

    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>> {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);
        let queue = (*data).as_mut()?;

        // Entries popped but not eligible for `cpu_id` *specifically* right
        // now (see the module doc) — held aside and re-pushed unchanged
        // before this call returns, so they remain available to whichever
        // cpu (possibly this same one, next time) they're actually eligible
        // for.
        let mut deferred: Vec<DeferredEntry> = Vec::new();

        let dispatched = loop {
            let Some((key, entry_cpu_set, mut entry)) = queue.pop_for_cpu(cpu_id) else {
                break None;
            };
            let Some(task) = entry.take() else {
                continue;
            };

            let active_set = {
                let mut node = MCSNode::new();
                let info = task.info.lock(&mut node);
                match info.scheduler_type {
                    SchedulerType::MixedVp(active_set, _, _) => active_set,
                    _ => unreachable!(),
                }
            };

            let eligible = if active_set.contains(cpu_id) {
                active_vp::active_eligible(cpu_id)
            } else {
                !passive_vp::active_vp_is_busy(cpu_id)
            };

            if !eligible {
                deferred.push((key.priority, entry_cpu_set, ClusteredTask::new(task)));
                continue;
            }

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
            drop(task_info);

            break Some(task);
        };

        for (priority, entry_cpu_set, entry) in deferred {
            let _ = queue.push(priority, entry_cpu_set, entry);
        }

        dispatched
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::MixedVp(CpuSet::empty(), 0, CpuSet::empty())
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

pub static SCHEDULER: MixedVpScheduler = MixedVpScheduler {
    data: Mutex::new(None),
    priority: get_priority(&SchedulerType::MixedVp(CpuSet::empty(), 0, CpuSet::empty())),
};

impl MixedVpScheduler {
    /// Identical in structure to `ClusteredEDFScheduler::invoke_preemption`
    /// (see that module): find the lowest-priority running-or-pending
    /// victim across `task`'s cpu_set (here, `active_set ∪ passive_set`)
    /// and preempt it if `task` outranks it. Safe to reuse verbatim across
    /// both halves of the union: on `task`'s own `active_set`, the only
    /// possible victim is a lower-priority leftover there (exclusive core
    /// ownership rules out any other DAG's active-VP task); on a borrowed
    /// `passive_set` core, `PriorityInfo`'s packed scheduler-class tier
    /// (`MixedVp` below `ActiveVp`) already prevents `task > target_task`
    /// from ever being true when `target_task` is that core's true
    /// active-VP owner.
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
