//! An EDF scheduler.
//!
//! Each task carries a [`CpuSet`] describing the CPU cores it may run on.
//! A one-core set gives partitioned EDF, and `CpuSet::all()` gives global EDF.
//! Runnable tasks are kept in two affinity-aware priority queues
//! ([`AffinityBTreeQueue`]), one for tasks that every worker core can run and
//! one for the other tasks; `get_next` on CPU `c` pops the earliest-deadline
//! task of either queue whose `cpu_set` contains `c`.

use super::{Scheduler, SchedulerType, Task};
use crate::{
    dag::calculate_and_update_dag_deadline,
    scheduler::{
        get_priority, peek_preemption_pending, push_preemption_pending, GLOBAL_WAKE_GET_MUTEX,
        PREEMPTION_ENABLED,
    },
    task::{
        get_task, get_task_running, set_current_task, set_need_preemption, State,
        MAX_TASK_PRIORITY, NUM_EDF_TASKS_IN_QUEUE,
    },
};
use affinity_btree_queue::{AffinityBTreeQueue, DEFAULT_MIN_DEGREE};
use alloc::sync::Arc;
use awkernel_lib::{
    cpu::{all_workers, masked_workers, num_cpu, CpuSet, CPU_SET_WORDS},
    sync::mutex::{MCSNode, Mutex},
};
use core::sync::atomic::Ordering;

/// Priority of a queued task, `(absolute_deadline, wake_time, seq)`. Smaller
/// values dequeue first. `seq` grows with each push, so entries with equal
/// deadlines and wake times are FIFO-ordered across both queues.
type Key = (u64, u64, u64);

type Queue<V> = AffinityBTreeQueue<Key, V, DEFAULT_MIN_DEGREE, CPU_SET_WORDS>;

/// The run queues of the EDF scheduler.
///
/// `wake_workers` wakes every core in the affinity mask of `restricted`, but
/// only one core for each task of `global`. A single queue would put every
/// worker in the mask while one task that every worker can run is queued.
struct EDFQueues<V> {
    /// Tasks whose set holds every worker core.
    global: Queue<V>,
    /// The other tasks.
    restricted: Queue<V>,
    next_seq: u64,
}

impl<V> EDFQueues<V> {
    fn new(num_cpus: usize) -> Self {
        Self {
            global: Queue::new(num_cpus),
            restricted: Queue::new(num_cpus),
            next_seq: 0,
        }
    }

    /// `priority` is `(absolute_deadline, wake_time)`.
    fn push(&mut self, priority: (u64, u64), cpu_set: CpuSet, value: V) {
        let key = (priority.0, priority.1, self.next_seq);
        self.next_seq += 1;

        let queue = if cpu_set == all_workers(self.global.num_cpus()) {
            &mut self.global
        } else {
            &mut self.restricted
        };
        queue
            .push(key, cpu_set, value)
            .expect("EDF: failed to push a task");
    }

    fn len(&self) -> usize {
        self.global.len() + self.restricted.len()
    }

    /// The key of the earliest queued task runnable on `cpu_id`.
    fn peek_for_cpu(&self, cpu_id: usize) -> Option<Key> {
        let global = self.global.peek_key_for_cpu(cpu_id).map(|k| k.priority);
        let restricted = self.restricted.peek_key_for_cpu(cpu_id).map(|k| k.priority);
        match (global, restricted) {
            (Some(g), Some(r)) => Some(g.min(r)),
            (g, r) => g.or(r),
        }
    }

    /// Remove and return the earliest queued task runnable on `cpu_id`.
    fn pop_for_cpu(&mut self, cpu_id: usize) -> Option<V> {
        let global = self.global.peek_key_for_cpu(cpu_id).map(|k| k.priority);
        let restricted = self.restricted.peek_key_for_cpu(cpu_id).map(|k| k.priority);
        let queue = match (global, restricted) {
            (None, None) => return None,
            (Some(g), Some(r)) if r < g => &mut self.restricted,
            (None, Some(_)) => &mut self.restricted,
            _ => &mut self.global,
        };
        queue.pop_for_cpu(cpu_id).map(|(_, _, value)| value)
    }
}

pub struct EDFScheduler {
    // `AffinityBTreeQueue::new` is not a const fn, so the queues are lazily
    // initialized with `num_cpu()` on first use.
    data: Mutex<Option<EDFQueues<QueuedTask<Arc<Task>>>>>,
    priority: u8,
}

/// RAII wrapper representing one slot in `NUM_EDF_TASKS_IN_QUEUE`.
///
/// Constructing a `QueuedTask` increments the counter. The counter is
/// decremented exactly once — either via [`take`] (explicit ownership
/// transfer) or via `Drop` (e.g. when a terminated task is discarded). If
/// `take` has already been called, `Drop` is a no-op.
///
/// [`take`]: QueuedTask::take
struct QueuedTask<T> {
    inner: Option<T>,
}

impl<T> QueuedTask<T> {
    fn new(inner: T) -> Self {
        NUM_EDF_TASKS_IN_QUEUE.fetch_add(1, Ordering::Relaxed);
        Self { inner: Some(inner) }
    }

    /// Take the inner value and decrement the counter.
    ///
    /// Returns `None` if the value has already been taken.
    /// After this call `Drop` will be a no-op.
    fn take(&mut self) -> Option<T> {
        let val = self.inner.take();
        if val.is_some() {
            NUM_EDF_TASKS_IN_QUEUE.fetch_sub(1, Ordering::Relaxed);
        }
        val
    }
}

impl<T> Drop for QueuedTask<T> {
    fn drop(&mut self) {
        // Decrement only if take() has not been called yet.
        if self.inner.is_some() {
            NUM_EDF_TASKS_IN_QUEUE.fetch_sub(1, Ordering::Relaxed);
        }
    }
}

impl Scheduler for EDFScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let (wake_time, absolute_deadline) = {
            let mut node_inner = MCSNode::new();
            let mut info = task.info.lock(&mut node_inner);
            let dag_info = info.get_dag_info();
            match info.scheduler_type {
                SchedulerType::EDF(relative_deadline, _) => {
                    let wake_time = awkernel_lib::delay::uptime();
                    let absolute_deadline = if let Some(ref dag_info) = dag_info {
                        calculate_and_update_dag_deadline(dag_info, wake_time, info.state)
                    } else {
                        // If dag_info is not present, the task is treated as a regular task, and
                        // the absolute_deadline is calculated using the scheduler's relative_deadline.
                        wake_time + relative_deadline
                    };

                    task.priority
                        .update_priority_info(self.priority, MAX_TASK_PRIORITY - absolute_deadline);
                    info.update_absolute_deadline(absolute_deadline);

                    (wake_time, absolute_deadline)
                }
                _ => unreachable!(),
            }
        };

        // `Tasks::spawn` is the single point that validates and normalizes the
        // set (masking to worker cores, falling back to all workers when empty).
        // Reaching here with an invalid set means that invariant was violated
        // internally, so fail loud rather than enqueue an unrunnable task.
        let cpu_set = task.cpu_set.expect("EDF task has no CPU set");
        if cpu_set.is_empty() || masked_workers(cpu_set, num_cpu()) != cpu_set {
            unreachable!("EDF: cpu_set {cpu_set:?} was not normalized by spawn");
        }

        let mut node = MCSNode::new();
        let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);
        if !self.invoke_preemption(task.clone(), (absolute_deadline, wake_time)) {
            let mut node_inner = MCSNode::new();
            let mut data = self.data.lock(&mut node_inner);
            let queues = data.get_or_insert_with(|| EDFQueues::new(num_cpu()));
            queues.push(
                (absolute_deadline, wake_time),
                cpu_set,
                QueuedTask::new(task),
            );
            drop(data);

            // `do_preemption` and `run_main` re-wake tasks through this function
            // without `ArcWake::wake`, so notify the primary CPU here to wake an
            // idle worker in the set.
            awkernel_lib::cpu::wake_cpu(0);
        }
    }

    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>> {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);
        let queues = (*data).as_mut()?;

        // Note: spawn removes CPU 0 from every set, so `pop_for_cpu(0)` always
        // returns `None` and the `get_next_task(false)` path executed on the
        // primary CPU can never dequeue an EDF task.
        loop {
            let mut entry = queues.pop_for_cpu(cpu_id)?;

            // take() decrements the counters; entry then drops with inner == None.
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
                    set_current_task(awkernel_lib::cpu::cpu_id(), task.id);
                }
            }

            return Some(task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::EDF(0, CpuSet::empty())
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

pub static SCHEDULER: EDFScheduler = EDFScheduler {
    data: Mutex::new(None),
    priority: get_priority(&SchedulerType::EDF(0, CpuSet::empty())),
};

impl EDFScheduler {
    /// The workers that queued tasks need, as `(mask, num_global)`.
    ///
    /// `mask` holds every CPU that a queued task restricted to some of the
    /// workers can run on. `num_global` is the number of queued tasks that
    /// every worker can run, so any `num_global` workers can run them.
    pub(crate) fn queued_workers(&self) -> (CpuSet, usize) {
        let mut node = MCSNode::new();
        let data = self.data.lock(&mut node);

        // O(1): each queue maintains the OR of all queued affinities in its
        // B-tree root.
        match &*data {
            Some(queues) => (queues.restricted.affinity_mask(), queues.global.len()),
            None => (CpuSet::empty(), 0),
        }
    }

    /// `key` is the queue priority of `task`, `(absolute_deadline, wake_time)`.
    fn invoke_preemption(&self, task: Arc<Task>, key: (u64, u64)) -> bool {
        if !PREEMPTION_ENABLED {
            return false;
        }

        let cpu_set = task.cpu_set.expect("Task has no CPU set");

        let mut idle_cpus = CpuSet::empty();
        for cpu_id in cpu_set.iter() {
            match get_task_running(cpu_id).task_id {
                // If the task has already been running, preempt is not required.
                id if id == task.id => return false,
                0 => idle_cpus.insert(cpu_id),
                _ => (),
            }
        }

        if !idle_cpus.is_empty() {
            let mut node = MCSNode::new();
            let data = self.data.lock(&mut node);
            if (*data)
                .as_ref()
                .is_none_or(|queues| idle_cpu_takes(queues, idle_cpus, key))
            {
                return false;
            }
        }

        // Find the CPU whose target (running or pending-preemption) task has
        // the lowest priority among the busy CPUs of the set.
        let mut victim: Option<(usize, Arc<Task>)> = None;

        for cpu_id in cpu_set.iter() {
            if idle_cpus.contains(cpu_id) {
                continue;
            }

            let task_running = get_task(get_task_running(cpu_id).task_id);
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

        if task.preempts(&target_task) {
            push_preemption_pending(victim_cpu, task);
            let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
            set_need_preemption(target_task.id, victim_cpu);
            awkernel_lib::interrupt::send_ipi(preempt_irq, victim_cpu as u32);

            // NOTE: The task is now pinned to `victim_cpu`'s preemption-pending
            // heap and is not in the affinity queue, so it is invisible to the
            // other CPUs in its `cpu_set` (neither `pop_for_cpu`,
            // `NUM_EDF_TASKS_IN_QUEUE`, nor `queued_workers` sees it). If another CPU in
            // the set becomes idle while the IPI is in flight, it cannot pick
            // the task up and may go to sleep — a latency window bounded by the
            // IPI delivery plus the victim's interrupt-disabled sections. This
            // is not a lost wakeup: the task is eventually run either by the
            // victim's preemption handler (`do_preemption`), or re-woken by the
            // victim's `run_main` if its running task finishes first, in which
            // case this function decides again. Future work:
            // an enqueue-instead-of-pin strategy (push to the affinity queue
            // and treat the IPI as a hint) would close this window, but it
            // requires redesigning the duplicate-IPI suppression that the
            // pending heap currently provides via `peek_preemption_pending`.

            return true;
        }

        false
    }
}

/// Whether a CPU of `idle_cpus` takes a task of priority `key` if the task is
/// pushed to `queues` now.
///
/// An idle CPU takes the earliest queued task runnable on it. So the task is
/// taken if it is earlier than every queued task runnable on one of
/// `idle_cpus`, or if `queues` hold fewer tasks than `idle_cpus` holds CPUs.
/// Otherwise, the queued tasks can take every idle CPU first, and the task
/// must preempt to run now.
fn idle_cpu_takes<V>(queues: &EDFQueues<V>, idle_cpus: CpuSet, key: (u64, u64)) -> bool {
    queues.len() < idle_cpus.iter().count()
        || idle_cpus.iter().any(|cpu_id| {
            queues
                .peek_for_cpu(cpu_id)
                .is_none_or(|(deadline, wake_time, _)| (deadline, wake_time) > key)
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    type Queues = EDFQueues<u32>;

    const IDLE_2: CpuSet = CpuSet::empty().with(2);
    /// Every worker core of a 4-CPU system.
    const ALL: CpuSet = CpuSet::empty().with(1).with(2).with(3);

    #[test]
    fn idle_cpu_takes_task_from_empty_queue() {
        assert!(idle_cpu_takes(&Queues::new(4), IDLE_2, (10, 0)));
    }

    #[test]
    fn earlier_queued_task_claims_the_only_idle_cpu() {
        let mut queues = Queues::new(4);
        queues.push((5, 0), ALL, 0);
        assert!(!idle_cpu_takes(&queues, IDLE_2, (10, 0)));
    }

    #[test]
    fn equal_key_is_fifo() {
        let mut queues = Queues::new(4);
        queues.push((10, 0), ALL, 0);
        assert!(!idle_cpu_takes(&queues, IDLE_2, (10, 0)));
    }

    #[test]
    fn task_earlier_than_queue_head_is_taken() {
        let mut queues = Queues::new(4);
        queues.push((20, 0), ALL, 0);
        assert!(idle_cpu_takes(&queues, IDLE_2, (10, 0)));
    }

    #[test]
    fn spare_idle_cpu_takes_task() {
        let mut queues = Queues::new(4);
        queues.push((5, 0), ALL, 0);
        assert!(idle_cpu_takes(&queues, IDLE_2.with(3), (10, 0)));
    }

    #[test]
    fn queued_task_of_another_cpu_does_not_claim_idle_cpu() {
        let mut queues = Queues::new(4);
        queues.push((5, 0), CpuSet::empty().with(3), 0);
        assert!(idle_cpu_takes(&queues, IDLE_2, (10, 0)));
    }

    #[test]
    fn pop_takes_earliest_task_of_either_queue() {
        let mut queues = Queues::new(4);
        queues.push((30, 0), ALL, 1);
        queues.push((10, 0), IDLE_2, 2);
        queues.push((20, 0), ALL, 3);
        assert_eq!(queues.pop_for_cpu(2), Some(2));
        assert_eq!(queues.pop_for_cpu(2), Some(3));
        assert_eq!(queues.pop_for_cpu(2), Some(1));
        assert_eq!(queues.pop_for_cpu(2), None);
    }

    #[test]
    fn equal_keys_are_fifo_across_queues() {
        let mut queues = Queues::new(4);
        queues.push((10, 0), ALL, 1);
        queues.push((10, 0), IDLE_2, 2);
        queues.push((10, 0), ALL, 3);
        assert_eq!(queues.pop_for_cpu(2), Some(1));
        assert_eq!(queues.pop_for_cpu(2), Some(2));
        assert_eq!(queues.pop_for_cpu(2), Some(3));
    }

    #[test]
    fn restricted_task_stays_off_other_cpus() {
        let mut queues = Queues::new(4);
        queues.push((10, 0), IDLE_2, 1);
        queues.push((20, 0), ALL, 2);
        assert_eq!(queues.pop_for_cpu(3), Some(2));
        assert_eq!(queues.pop_for_cpu(3), None);
        assert_eq!(queues.pop_for_cpu(2), Some(1));
    }

    #[test]
    fn global_task_stays_out_of_restricted_mask() {
        let mut queues = Queues::new(4);
        queues.push((10, 0), ALL, 1);
        queues.push((20, 0), IDLE_2, 2);
        assert_eq!(queues.restricted.affinity_mask(), IDLE_2);
        assert_eq!(queues.global.len(), 1);
    }
}
