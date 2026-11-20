//! Shared affinity queue and preemption code for the clustered schedulers.
//!
//! Each task carries a [`CpuSet`] describing the CPU cores it may run on.
//! Runnable tasks are kept in a single affinity-aware priority queue
//! ([`AffinityBTreeQueue`]) per scheduler type.

use super::{Scheduler, SchedulerType, Task};
use crate::{
    scheduler::{
        get_priority, peek_preemption_pending, push_preemption_pending, ClusteredTask,
        GLOBAL_WAKE_GET_MUTEX, PREEMPTION_ENABLED,
    },
    task::{
        get_task, get_task_running, set_current_task, set_need_preemption, State, TaskInfo,
        MAX_TASK_PRIORITY,
    },
};
use core::marker::PhantomData;

use affinity_btree_queue::{AffinityBTreeQueue, DEFAULT_MIN_DEGREE};
use alloc::sync::Arc;
use awkernel_lib::{
    cpu::{masked_workers, num_cpu, CpuSet, CPU_SET_WORDS},
    sync::mutex::{MCSNode, Mutex},
};
/// The run queue. Priority is `(ordering_time, wake_time)`; smaller values
/// dequeue first, and entries with fully equal keys are FIFO-ordered by the
/// queue's internal sequence number.
type ReadyQueue =
    AffinityBTreeQueue<(u64, u64), ClusteredTask<Arc<Task>>, DEFAULT_MIN_DEGREE, CPU_SET_WORDS>;

pub(super) trait ClusteredOrdering {
    const KIND: SchedulerType;

    /// Called once per wake under the task info lock. Return the real
    /// deadline and queue ordering time.
    fn ready_priority(info: &TaskInfo, wake_time: u64) -> (u64, u64);
}

pub(super) struct ClusteredScheduler<O: ClusteredOrdering> {
    // `AffinityBTreeQueue::new` is not a const fn, so the queue is lazily
    // initialized with `num_cpu()` on first use.
    data: Mutex<Option<ReadyQueue>>,
    priority: u8,
    ordering: PhantomData<fn() -> O>,
}

impl<O: ClusteredOrdering> Scheduler for ClusteredScheduler<O> {
    // Queue operations can allocate and contend. Victim selection scans at
    // most the CPUs in the affinity set.
    fn wake_task(&self, task: Arc<Task>) {
        let key = {
            let mut node_inner = MCSNode::new();
            let mut info = task.info.lock(&mut node_inner);
            let wake_time = awkernel_lib::delay::uptime();
            let (absolute_deadline, ordering_time) = O::ready_priority(&info, wake_time);
            task.priority
                .update_priority_info(self.priority, MAX_TASK_PRIORITY - ordering_time);
            info.update_absolute_deadline(absolute_deadline);
            (ordering_time, wake_time)
        };

        // `Tasks::spawn` is the single point that validates and normalizes the
        // set (masking to worker cores, falling back to all workers when empty).
        // Reaching here with an invalid set means that invariant was violated
        // internally, so fail loud rather than enqueue an unrunnable task.
        let cpu_set = task.cpu_set.expect("clustered task has no CPU set");
        if cpu_set.is_empty() || masked_workers(cpu_set, num_cpu()) != cpu_set {
            unreachable!("clustered scheduler: cpu_set {cpu_set:?} was not normalized by spawn");
        }

        let mut node = MCSNode::new();
        let _guard = GLOBAL_WAKE_GET_MUTEX.lock(&mut node);
        if !self.invoke_preemption(task.clone()) {
            let mut node_inner = MCSNode::new();
            let mut data = self.data.lock(&mut node_inner);
            let queue = data.get_or_insert_with(|| ReadyQueue::new(num_cpu()));
            queue
                .push(key, cpu_set, ClusteredTask::new(task))
                .expect("clustered scheduler: failed to push a task");
            drop(data);

            // Every enqueue goes through this function, including the re-wakes
            // that bypass `ArcWake::wake`, so notify the primary CPU here to
            // wake an idle worker in the set.
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
        O::KIND
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

impl<O: ClusteredOrdering> ClusteredScheduler<O> {
    pub(super) const fn new() -> Self {
        Self {
            data: Mutex::new(None),
            priority: get_priority(&O::KIND),
            ordering: PhantomData,
        }
    }

    fn invoke_preemption(&self, task: Arc<Task>) -> bool {
        if !PREEMPTION_ENABLED {
            return false;
        }

        let cpu_set = task.cpu_set.expect("Task has no CPU set");

        // Find the CPU whose target (running or pending-preemption) task has
        // the lowest priority among the busy CPUs of the set.
        let mut victim: Option<(usize, Arc<Task>)> = None;

        for cpu_id in cpu_set.iter() {
            let task_running = get_task_running(cpu_id);

            // If the task has already been running, preempt is not required.
            if task_running.task_id == task.id {
                return false;
            }

            // An idle CPU does not stop the preemption. A task queued before
            // or after this one can take the idle CPU first, and a sleeping
            // CPU runs a queued task only after the primary CPU wakes it. So
            // this task can preempt the lowest-priority busy CPU even if the
            // set has an idle CPU. The cost is that the preemption can be
            // unneeded, and the victim waits for the primary CPU to wake a
            // sleeping CPU. If the set of the victim holds no idle CPU, the
            // victim waits for its own CPU while the idle CPU stays idle.
            if task_running.task_id == 0 {
                continue;
            }

            // A running task that is missing from the task table finished
            // after the read above, so this CPU counts as idle too.
            let Some(task_running) = get_task(task_running.task_id) else {
                continue;
            };

            let target_task = match peek_preemption_pending(cpu_id) {
                Some(pending) => task_running.max(pending),
                None => task_running,
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
            // the set is or becomes idle while the IPI is in flight, it cannot pick
            // the task up and may go to sleep — a latency window bounded by the
            // IPI delivery plus the victim's interrupt-disabled sections. This
            // is not a lost wakeup: the task is eventually run either by the
            // victim's preemption handler (`do_preemption`), or re-woken by the
            // victim's `run_main` if its running task finishes first, in which
            // case this function decides again. `run_main` checks the pending
            // heap again before the victim sleeps. Future work:
            // an enqueue-instead-of-pin strategy (push to the affinity queue
            // and treat the IPI as a hint) would close this window, but it
            // requires redesigning the duplicate-IPI suppression that the
            // pending heap currently provides via `peek_preemption_pending`.

            return true;
        }

        false
    }
}
