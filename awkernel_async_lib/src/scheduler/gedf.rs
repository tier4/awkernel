//! A GEDF scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task::{get_tasks_running, set_need_preemption, State};
use alloc::{
    collections::{BTreeMap, BinaryHeap},
    sync::Arc,
};
use awkernel_lib::{
    cpu::num_cpu,
    sync::mutex::{MCSNode, Mutex},
};

pub struct GEDFScheduler {
    data: Mutex<Option<GEDFData>>,      // Run queue.
    manager: Mutex<BTreeMap<u32, u64>>, // Task ID, Absolute Deadline
}

struct GEDFTask {
    task: Arc<Task>,
    absolute_deadline: u64,
    wake_time: u64,
}

impl PartialOrd for GEDFTask {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for GEDFTask {
    fn eq(&self, other: &Self) -> bool {
        self.absolute_deadline == other.absolute_deadline && self.wake_time == other.wake_time
    }
}

impl Ord for GEDFTask {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        match other.absolute_deadline.cmp(&self.absolute_deadline) {
            core::cmp::Ordering::Equal => other.wake_time.cmp(&self.wake_time),
            other => other,
        }
    }
}

impl Eq for GEDFTask {}

struct GEDFData {
    queue: BinaryHeap<GEDFTask>,
}

impl GEDFData {
    fn new() -> Self {
        Self {
            queue: BinaryHeap::new(),
        }
    }
}

impl Scheduler for GEDFScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);
        let data = data.get_or_insert_with(GEDFData::new);

        self.remove_manager();

        let mut node = MCSNode::new();
        let info = task.info.lock(&mut node);

        let SchedulerType::GEDF(relative_deadline) = info.scheduler_type else {
            unreachable!();
        };

        let wake_time = awkernel_lib::delay::uptime();
        let absolute_deadline = wake_time + relative_deadline;

        data.queue.push(GEDFTask {
            task: task.clone(),
            absolute_deadline,
            wake_time,
        });

        log::info!(
            "wake task_id: {}",
            task.id
        );

        self.insert_manager(task.id, absolute_deadline);
        self.need_preempt(absolute_deadline);
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = match data.as_mut() {
            Some(data) => data,
            None => return None,
        };

        loop {
            // Pop a task from the run queue.
            let task = data.queue.pop()?;

            // Make the state of the task Running.
            {
                let mut node = MCSNode::new();
                let mut task_info = task.task.info.lock(&mut node);

                if matches!(task_info.state, State::Terminated | State::Panicked) {
                    continue;
                }

                task_info.state = State::Running;
            }

            return Some(task.task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::GEDF(0)
    }

    // TODO: Priority implementation between schedulers.
    fn priority(&self) -> u8 {
        0
    }
}

pub static SCHEDULER: GEDFScheduler = GEDFScheduler {
    data: Mutex::new(None),
    manager: Mutex::new(BTreeMap::new()),
};

impl GEDFScheduler {
    fn insert_manager(&self, task_id: u32, absolute_deadline: u64) {
        let mut node = MCSNode::new();
        let mut manager = self.manager.lock(&mut node);
        manager.insert(task_id, absolute_deadline);
    }

    fn remove_manager(&self) {
        let mut node = MCSNode::new();
        let mut manager = self.manager.lock(&mut node);
        let now = awkernel_lib::delay::uptime();
        manager.retain(|_, deadline| *deadline > now);
    }

    /// Return CPU ID to preempt.
    fn need_preempt(&self, absolute_deadline: u64) {
        // Get running tasks and filter out tasks with task_id == 0.
        let mut tasks = get_tasks_running();
        tasks.retain(|task| task.task_id != 0);

        // log::info!("tasks: {:?}", tasks);

        // If the number of running tasks is less than the number of non-primary CPUs, preempt is not required.
        if tasks.len() < num_cpu() - 1 {
            return;
        }

        // Check the priority of the task with the absolute deadline.
        let mut node = MCSNode::new();
        let manager = self.manager.lock(&mut node);
        if let Some((max_task_id, &max_deadline)) =
            manager.iter().max_by_key(|(_, &deadline)| deadline)
        {
            if max_deadline <= absolute_deadline {
                return;
            }
            if let Some(task) = tasks.iter().find(|task| task.task_id == *max_task_id) {
                self.invoke_preemption(task.cpu_id, task.task_id);
            }
        }
    }

    fn invoke_preemption(&self, cpu_id: usize, task_id: u32) {
        let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
        set_need_preemption(task_id);
        awkernel_lib::interrupt::send_ipi(preempt_irq, cpu_id as u32);
    }
}
