//! An EDF scheduler.
//!
//! Each task carries a [`CpuSet`] describing the CPU cores it may run on.
//! A one-core set gives partitioned EDF, and `CpuSet::all()` gives global EDF.
//! Runnable tasks are kept in a single affinity-aware priority queue
//! ([`AffinityBTreeQueue`]); `get_next` on CPU `c` pops the earliest-deadline
//! task whose `cpu_set` contains `c`.

use super::{Scheduler, SchedulerType, Task};
use crate::{
    dag::calculate_and_update_dag_deadline,
    scheduler::{
        get_priority, peek_preemption_pending, push_preemption_pending, ClusteredTask,
        GLOBAL_WAKE_GET_MUTEX, PREEMPTION_ENABLED,
    },
    task::{
        get_task, get_task_running, set_current_task, set_need_preemption, State, MAX_TASK_PRIORITY,
    },
};
use affinity_btree_queue::{AffinityBTreeQueue, DEFAULT_MIN_DEGREE};
use alloc::sync::Arc;
use awkernel_lib::{
    cpu::{masked_workers, num_cpu, CpuSet, CPU_SET_WORDS},
    sync::mutex::{MCSNode, Mutex},
};

/// The run queue. Priority is `(absolute_deadline, wake_time)`; smaller values
/// dequeue first, and entries with fully equal keys are FIFO-ordered by the
/// queue's internal sequence number.
type EDFQueue =
    AffinityBTreeQueue<(u64, u64), ClusteredTask<Arc<Task>>, DEFAULT_MIN_DEGREE, CPU_SET_WORDS>;

pub struct EDFScheduler {
    // `AffinityBTreeQueue::new` is not a const fn, so the queue is lazily
    // initialized with `num_cpu()` on first use.
    data: Mutex<Option<EDFQueue>>,
    priority: u8,
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
            let queue = data.get_or_insert_with(|| EDFQueue::new(num_cpu()));
            queue
                .push(
                    (absolute_deadline, wake_time),
                    cpu_set,
                    ClusteredTask::new(task),
                )
                .expect("EDF: failed to push a task");
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
        let queue = (*data).as_mut()?;

        // Note: spawn removes CPU 0 from every set, so `pop_for_cpu(0)` always
        // returns `None` and the `get_next_task(false)` path executed on the
        // primary CPU can never dequeue a clustered task.
        loop {
            let (_, _, mut entry) = queue.pop_for_cpu(cpu_id)?;

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

    fn queued_cpu_mask(&self) -> CpuSet {
        let mut node = MCSNode::new();
        let data = self.data.lock(&mut node);

        // O(1): the queue maintains the OR of all queued affinities in its
        // B-tree root.
        match &*data {
            Some(queue) => queue.affinity_mask(),
            None => CpuSet::empty(),
        }
    }
}

pub static SCHEDULER: EDFScheduler = EDFScheduler {
    data: Mutex::new(None),
    priority: get_priority(&SchedulerType::EDF(0, CpuSet::empty())),
};

impl EDFScheduler {
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
                .is_none_or(|queue| idle_cpu_takes(queue, idle_cpus, key))
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
            // other CPUs in its `cpu_set` (neither `pop_for_cpu`, the clustered
            // task counter, nor `queued_cpu_mask` sees it). If another CPU in
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
/// pushed to `queue` now.
///
/// An idle CPU takes the earliest queued task runnable on it. So the task is
/// taken if it is earlier than every queued task runnable on one of
/// `idle_cpus`, or if `queue` holds fewer tasks than `idle_cpus` holds CPUs.
/// Otherwise, the queued tasks can take every idle CPU first, and the task
/// must preempt to run now.
fn idle_cpu_takes<V>(
    queue: &AffinityBTreeQueue<(u64, u64), V, DEFAULT_MIN_DEGREE, CPU_SET_WORDS>,
    idle_cpus: CpuSet,
    key: (u64, u64),
) -> bool {
    queue.len() < idle_cpus.iter().count()
        || idle_cpus.iter().any(|cpu_id| {
            queue
                .peek_key_for_cpu(cpu_id)
                .is_none_or(|queued| queued.priority > key)
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    type Queue = AffinityBTreeQueue<(u64, u64), (), DEFAULT_MIN_DEGREE, CPU_SET_WORDS>;

    const IDLE_2: CpuSet = CpuSet::empty().with(2);
    const ALL: CpuSet = CpuSet::empty().with(1).with(2).with(3);

    #[test]
    fn idle_cpu_takes_task_from_empty_queue() {
        assert!(idle_cpu_takes(&Queue::new(4), IDLE_2, (10, 0)));
    }

    #[test]
    fn earlier_queued_task_claims_the_only_idle_cpu() {
        let mut queue = Queue::new(4);
        queue.push((5, 0), ALL, ()).unwrap();
        assert!(!idle_cpu_takes(&queue, IDLE_2, (10, 0)));
    }

    #[test]
    fn equal_key_is_fifo() {
        let mut queue = Queue::new(4);
        queue.push((10, 0), ALL, ()).unwrap();
        assert!(!idle_cpu_takes(&queue, IDLE_2, (10, 0)));
    }

    #[test]
    fn task_earlier_than_queue_head_is_taken() {
        let mut queue = Queue::new(4);
        queue.push((20, 0), ALL, ()).unwrap();
        assert!(idle_cpu_takes(&queue, IDLE_2, (10, 0)));
    }

    #[test]
    fn spare_idle_cpu_takes_task() {
        let mut queue = Queue::new(4);
        queue.push((5, 0), ALL, ()).unwrap();
        assert!(idle_cpu_takes(&queue, IDLE_2.with(3), (10, 0)));
    }

    #[test]
    fn queued_task_of_another_cpu_does_not_claim_idle_cpu() {
        let mut queue = Queue::new(4);
        queue.push((5, 0), CpuSet::empty().with(3), ()).unwrap();
        assert!(idle_cpu_takes(&queue, IDLE_2, (10, 0)));
    }
}
