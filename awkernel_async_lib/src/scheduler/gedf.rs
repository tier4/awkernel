//! A GEDF scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task::State;
use alloc::collections::BTreeMap;
use alloc::{collections::BinaryHeap, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct GEDFScheduler {
    data: Mutex<Option<GEDFData>>, // runnable_queue and waiting_queue.
    ignition_counter: Mutex<IgnitionCounter>, // task_id -> ignition_count
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
        self.priority == other.priority && self.wake_time == other.wake_time
    }
}

impl Ord for GEDFTask {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        match self.priority.cmp(&other.priority).reverse() {
            core::cmp::Ordering::Equal => self.wake_time.cmp(&other.wake_time).reverse(),
            other => other,
        }
    }
}

impl Eq for GEDFTask {}

struct GEDFData {
    runnable_queue: BinaryHeap<GEDFTask>,
    waiting_queue: BinaryHeap<GEDFTask>,
}

impl GEDFData {
    fn new() -> Self {
        Self {
            runnable_queue: BinaryHeap::new(),
        }
    }
}

impl Scheduler for GEDFScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        if let Some(data) = data.as_mut() {
            let mut node = MCSNode::new();
            let info = task.info.lock(&mut node);
            let SchedulerType::GEDFScheduler(relative_deadline) = info.scheduler_type else {
                return;
            };

            let wake_time = awkernel_lib::delay::uptime();
            let absolute_deadline = wake_time + relative_deadline;

            data.queue.push(GEDFTask {
                task: task.clone(),
                absolute_deadline,
                wake_time,
            });
        } else {
            let mut gedf_data = GEDFData::new();
            let mut node = MCSNode::new();
            let info = task.info.lock(&mut node);
            let SchedulerType::GEDFScheduler(relative_deadline) = info.scheduler_type else {
                return;
            };

            let wake_time = awkernel_lib::delay::uptime();
            let absolute_deadline = wake_time + relative_deadline;

            data.queue.push(GEDFTask {
                task: task.clone(),
                absolute_deadline,
                wake_time,
            });
            *data = Some(gedf_data);
        }
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = match data.as_mut() {
            Some(data) => data,
            None => return None,
        };

        loop {
            // Pop a task from the run runnable_queue.
            let task = data.runnable_queue.pop()?;

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

    fn priority(&self) -> u8 {
        0
    }
}

pub static SCHEDULER: GEDFScheduler = GEDFScheduler {
    data: Mutex::new(None),
};
