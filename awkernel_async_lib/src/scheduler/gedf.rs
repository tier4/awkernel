//! A GEDF scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::task::State;
use alloc::collections::BTreeMap;
use alloc::{collections::BinaryHeap, sync::Arc};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

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

    fn get_ignition_count(&self, task_id: u32) -> Option<u64> {
        self.tasks.get(&task_id).copied()
    }

    fn ignition_task(&mut self, task_id: u32) {
        if let Some(ignition_count) = self.tasks.get_mut(&task_id) {
            *ignition_count += 1;
        }
    }
}

pub struct GEDFScheduler {
    data: Mutex<Option<GEDFData>>,    // Run runnable_queue.
    task_manager: Mutex<TaskManager>, // task_id -> ignition_count
}

struct GEDFTask {
    task: Arc<Task>,
    priority: u64, // Absolute deadline or runnable time.
    timestamp: u64,
}

impl PartialOrd for GEDFTask {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for GEDFTask {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority && self.timestamp == other.timestamp
    }
}

impl Ord for GEDFTask {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        match self.priority.cmp(&other.priority).reverse() {
            core::cmp::Ordering::Equal => self.timestamp.cmp(&other.timestamp).reverse(),
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
            waiting_queue: BinaryHeap::new(),
        }
    }
}

impl Scheduler for GEDFScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let mut node = MCSNode::new();
        let mut task_manager = self.task_manager.lock(&mut node);

        let mut node = MCSNode::new();
        let mut info = task.info.lock(&mut node);
        let SchedulerType::GEDF(period, relative_deadline, base_time) = info.scheduler_type else {
            return;
        };

        let task_id = task.id;
        task_manager.add_task(task_id);
        let ignition_count = task_manager.get_ignition_count(task_id).unwrap_or(0);
        let runnable_time = base_time + period * ignition_count;
        let absolute_deadline = runnable_time + relative_deadline;

        log::debug!(
            "task_id={}, ignition_count={}, absolute_deadline={}",
            task_id,
            ignition_count,
            absolute_deadline
        );

        if let Some(data) = data.as_mut() {
            if runnable_time > awkernel_lib::delay::uptime() {
                info.state = State::Waiting;
                data.waiting_queue.push(GEDFTask {
                    task: task.clone(),
                    priority: runnable_time,
                    timestamp: awkernel_lib::delay::uptime(),
                });
                return;
            } else {
                info.state = State::Runnable;
                data.runnable_queue.push(GEDFTask {
                    task: task.clone(),
                    priority: absolute_deadline,
                    timestamp: awkernel_lib::delay::uptime(),
                });
                // TODO: preempt process
            }
        } else {
            let mut gedf_data = GEDFData::new();
            gedf_data.runnable_queue.push(GEDFTask {
                task: task.clone(),
                priority: absolute_deadline,
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
        SchedulerType::GEDF(0, 0, 0)
    }

    fn priority(&self) -> u8 {
        0
    }
}

pub static SCHEDULER: GEDFScheduler = GEDFScheduler {
    data: Mutex::new(None),
    task_manager: Mutex::new(TaskManager::new()),
};

impl GEDFScheduler {
    pub fn check_waiting_queue(&self) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = match data.as_mut() {
            Some(data) => data,
            None => return,
        };

        loop {
            let top_task = match data.waiting_queue.peek() {
                Some(task) => task,
                None => break,
            };

            if top_task.priority > awkernel_lib::delay::uptime() {
                // TODO: preempt process
                break;
            }

            if let Some(mut task) = data.waiting_queue.pop() {
                self.set_task_runnable(&mut task);
                data.runnable_queue.push(task);
            }
        }
    }

    fn set_task_runnable(&self, task: &mut GEDFTask) {
        let mut node = MCSNode::new();
        let mut task_info = task.task.info.lock(&mut node);
        task_info.state = State::Runnable;
    }

    pub fn ignition_task(&self, task_id: u32) {
        let mut node = MCSNode::new();
        let mut task_manager = self.task_manager.lock(&mut node);

        task_manager.ignition_task(task_id);
    }
}
