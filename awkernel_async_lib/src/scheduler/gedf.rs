//! A GEDF scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task::State;
use alloc::{collections::BinaryHeap, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use alloc::collections::BTreeMap;

static TASKMANAGER: Mutex<TaskManager> = Mutex::new(TaskManager::new());

#[derive(Default)]
struct TaskManager {
    tasks: BTreeMap<u32, u64>, // task_id -> ignition_count
}

impl TaskManager {
    const fn new() -> Self {
        TaskManager {
            tasks: BTreeMap::new(),
        }
    }

    fn add_task(&mut self, task_id: u32) {
        self.tasks.entry(task_id).or_insert(0);
    }

    fn ignition_task(&mut self, task_id: u32) {
        if let Some(fire_count) = self.tasks.get_mut(&task_id) {
            *fire_count += 1;
        }
    }

    // タスクの発火回数を取得
    fn get_ignition_count(&self, task_id: u32) -> Option<u64> {
        self.tasks.get(&task_id).copied()
    }
}


pub struct GEDFScheduler {
    data: Mutex<Option<GEDFData>>, // Run queue.
}

struct GEDFTask {
    task: Arc<Task>,
    absolute_deadline: u64,
    timestamp: u64,
}

impl PartialOrd for GEDFTask {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for GEDFTask {
    fn eq(&self, other: &Self) -> bool {
        self.absolute_deadline == other.absolute_deadline && self.timestamp == other.timestamp
    }
}

impl Ord for GEDFTask {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        match self.absolute_deadline.cmp(&other.absolute_deadline).reverse() {
            core::cmp::Ordering::Equal => self.timestamp.cmp(&other.timestamp).reverse(),
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

        let mut task_manager_node = MCSNode::new();
        let mut task_manager = TASKMANAGER.lock(&mut task_manager_node);

        let mut node = MCSNode::new();
        let info = task.info.lock(&mut node);
        let SchedulerType::GEDF(period, relative_deadline) = info.scheduler_type else {
            return;
        };

        let task_id = task.id;
        task_manager.add_task(task_id);
        let ignition_count = task_manager.get_ignition_count(task_id).unwrap_or(0);
        let absolute_deadline = relative_deadline + period * ignition_count;
        task_manager.ignition_task(task_id);

        //log::debug!("task_id={}, ignition_count={}, absolute_deadline={}", task_id, ignition_count, absolute_deadline);

        if let Some(data) = data.as_mut() {
            data.queue.push(GEDFTask {
                task: task.clone(),
                absolute_deadline,
                timestamp: awkernel_lib::delay::uptime(),
            });
        } else {
            let mut gedf_data = GEDFData::new();
            gedf_data.queue.push(GEDFTask {
                task: task.clone(),
                absolute_deadline,
                timestamp: awkernel_lib::delay::uptime(),
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
        SchedulerType::GEDF(0,0)
    }

    fn priority(&self) -> u8 {
        0
    }
}

pub static SCHEDULER: GEDFScheduler = GEDFScheduler {
    data: Mutex::new(None),
};
