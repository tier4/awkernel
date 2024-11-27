//! A GEDF scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task::{
    get_absolute_deadline_by_task_id, get_tasks_running, set_need_preemption, State,
};
use alloc::{collections::BinaryHeap, sync::Arc};
use awkernel_lib::{
    cpu::num_cpu,
    sync::mutex::{MCSNode, Mutex},
};

pub struct GEDFScheduler {
    data: Mutex<Option<GEDFData>>, // Run queue.
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

        let mut node = MCSNode::new();
        let mut info = task.info.lock(&mut node);

        let SchedulerType::GEDF(relative_deadline) = info.get_scheduler_type() else {
            unreachable!();
        };

        let wake_time = awkernel_lib::delay::uptime();
        let absolute_deadline = wake_time + relative_deadline;

        info.update_absolute_deadline(absolute_deadline);

        data.queue.push(GEDFTask {
            task: task.clone(),
            absolute_deadline,
            wake_time,
        });

        self.invoke_preemption(absolute_deadline);
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
};

impl GEDFScheduler {
    fn invoke_preemption(&self, absolute_deadline: u64) {
        // Get running tasks and filter out tasks with task_id == 0.
        let mut tasks = get_tasks_running();
        tasks.retain(|task| task.task_id != 0);

        // If the number of running tasks is less than the number of non-primary CPUs, preempt is not required.
        let num_non_primary_cpus = num_cpu() - 1;
        if tasks.len() < num_non_primary_cpus {
            return;
        }

        let max_task_and_deadline = tasks
            .iter()
            .filter_map(|task| {
                get_absolute_deadline_by_task_id(task.task_id).map(|deadline| (task, deadline))
            })
            .max_by_key(|&(_, deadline)| deadline);

        if let Some((max_task, max_deadline)) = max_task_and_deadline {
            if max_deadline > absolute_deadline {
                let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
                set_need_preemption(max_task.task_id);
                awkernel_lib::interrupt::send_ipi(preempt_irq, max_task.cpu_id as u32);
            }
        }
    }
}
