//! A Clustered EDF scheduler.
//!
//! Each task carries a [`CpuSet`] describing the CPU cores it may run on.
//! Runnable tasks are kept in a single affinity-aware priority queue
//! ([`AffinityBTreeQueue`]); `get_next` on CPU `c` pops the earliest-deadline
//! task whose `cpu_set` contains `c`.

use super::{Scheduler, SchedulerType, Task};
use crate::{
    scheduler::{
        gedf::calculate_and_update_dag_deadline, get_priority, peek_preemption_pending,
        push_preemption_pending, ClusteredTask, GLOBAL_WAKE_GET_MUTEX,
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

pub struct ClusteredEDFScheduler {
    // `AffinityBTreeQueue::new` is not a const fn, so the queue is lazily
    // initialized with `num_cpu()` on first use.
    data: Mutex<Option<EDFQueue>>,
    priority: u8,
}

impl Scheduler for ClusteredEDFScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let (wake_time, absolute_deadline) = {
            let mut node_inner = MCSNode::new();
            let mut info = task.info.lock(&mut node_inner);
            let dag_info = info.get_dag_info();
            match info.scheduler_type {
                SchedulerType::ClusteredEDF(relative_deadline, _) => {
                    let wake_time = awkernel_lib::delay::uptime();
                    let absolute_deadline = if let Some(ref dag_info) = dag_info {
                        calculate_and_update_dag_deadline(dag_info, wake_time)
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

        // `Tasks::spawn` normalizes the set to worker cores (1..num_cpu()),
        // so an invalid set here is an internal invariant violation.
        let cpu_set = task.cpu_set.expect("Task has no CPU set");
        if cpu_set.is_empty() || masked_workers(cpu_set, num_cpu()) != cpu_set {
            panic!("ClusteredEDF: CPU set {cpu_set:?} is out of range");
        }

        let mut node = MCSNode::new();
        let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);
        if !self.invoke_preemption(task.clone()) {
            let mut node_inner = MCSNode::new();
            let mut data = self.data.lock(&mut node_inner);
            let queue = data.get_or_insert_with(|| EDFQueue::new(num_cpu()));
            queue
                .push(
                    (absolute_deadline, wake_time),
                    cpu_set,
                    ClusteredTask::new(task.clone()),
                )
                .expect("ClusteredEDF: failed to push a task");
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
        SchedulerType::ClusteredEDF(0, CpuSet::empty())
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

pub static SCHEDULER: ClusteredEDFScheduler = ClusteredEDFScheduler {
    data: Mutex::new(None),
    priority: get_priority(SchedulerType::ClusteredEDF(0, CpuSet::empty())),
};

impl ClusteredEDFScheduler {
    fn invoke_preemption(&self, task: Arc<Task>) -> bool {
        let cpu_set = task.cpu_set.expect("Task has no CPU set");

        // Find the CPU whose target (running or pending-preemption) task has
        // the lowest priority among the set.
        let mut victim: Option<(usize, Arc<Task>)> = None;

        for cpu_id in cpu_set.iter() {
            let task_running = get_task_running(cpu_id);

            // If the task has already been running, preempt is not required.
            if task_running.task_id == task.id {
                return false;
            }

            // An idle CPU in the set will pick the task up; no preemption needed.
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

            // NOTE(atsushi421): Currently, preemption is requested regardless of the number of idle CPUs.
            // While this implementation easily prevents priority inversion, it may also cause unnecessary preemption.
            // Therefore, a more sophisticated implementation will be considered in the future.

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
            // case the idle check above routes it to the queue. Future work:
            // an enqueue-instead-of-pin strategy (push to the affinity queue
            // and treat the IPI as a hint) would close this window, but it
            // requires redesigning the duplicate-IPI suppression that the
            // pending heap currently provides via `peek_preemption_pending`.

            return true;
        }

        false
    }
}
