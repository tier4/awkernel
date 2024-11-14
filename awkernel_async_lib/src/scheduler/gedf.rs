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

/// A GEDF task has two types of priority attributes:
/// - priority: This can represent either an absolute deadline or a release time:
///   - absolute deadline: The time when the task must be completed. Runnable tasks have absolute deadline.
///   - release time: The time when the task becomes release. Waiting tasks have release time.
/// - timestamp: The time when the task is enqueued.
// The task with the highest priority is executed first.
// If two tasks have the same priority, the task with the earliest timestamp is executed first.
struct GEDFTask {
    task: Arc<Task>,
    priority: u64,
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

#[derive(Default)]
struct IgnitionCounter {
    ignition_counts: BTreeMap<u32, u64>, // task_id -> ignition_count
}

impl IgnitionCounter {
    const fn new() -> Self {
        IgnitionCounter {
            ignition_counts: BTreeMap::new(),
        }
    }

    /// Used immediately after the start of a periodic task.
    fn register_task(&mut self, task_id: u32) {
        self.ignition_counts.entry(task_id).or_insert(0);
    }

    fn get_ignition_count(&self, task_id: u32) -> u64 {
        *self.ignition_counts.get(&task_id).unwrap_or(&0)
    }

    /// Used when the periodic task is executed.
    fn increment_ignition(&mut self, task_id: u32) {
        if let Some(ignition_count) = self.ignition_counts.get_mut(&task_id) {
            *ignition_count += 1;
        }
    }
}

impl Scheduler for GEDFScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let (release_time, absolute_deadline) = self.calculate_release_and_deadline(&task);

        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);
        if let Some(data) = data.as_mut() {
            // Determine whether a task is executable and enqueue it to a suitable queue.
            let task_state = if release_time > awkernel_lib::delay::uptime() {
                State::Waiting
            } else {
                State::Runnable
            };

            let priority = if task_state == State::Waiting {
                release_time
            } else {
                absolute_deadline
            };

            let queue = if task_state == State::Waiting {
                &mut data.waiting_queue
            } else {
                &mut data.runnable_queue
            };

            let mut task = task.clone();
            self.set_task_state(&mut task, task_state);

            queue.push(GEDFTask {
                task,
                priority,
                timestamp: awkernel_lib::delay::uptime(),
            });
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
    ignition_counter: Mutex::new(IgnitionCounter::new()),
};

impl GEDFScheduler {
    fn get_gedf_params(&self, task: &Arc<Task>) -> (u64, u64, u64) {
        let mut node = MCSNode::new();
        let info = task.info.lock(&mut node);
        if let SchedulerType::GEDF(period, relative_deadline, spawn_time) = info.scheduler_type {
            (period, relative_deadline, spawn_time)
        } else {
            // Unreachable
            panic!("Expected SchedulerType::GEDF, but found a different type.");
        }
    }

    fn calculate_release_and_deadline(&self, task: &Arc<Task>) -> (u64, u64) {
        let (period, relative_deadline, spawn_time) = self.get_gedf_params(task);
        let ignition_count = {
            let mut node = MCSNode::new();
            let ignition_counter = self.ignition_counter.lock(&mut node);
            ignition_counter.get_ignition_count(task.id)
        };
        let release_time = spawn_time + period * ignition_count;
        let absolute_deadline = release_time + relative_deadline;
        (release_time, absolute_deadline)
    }

    fn set_task_state(&self, task: &mut Arc<Task>, task_state: State) {
        let mut node = MCSNode::new();
        let mut info = task.info.lock(&mut node);
        info.state = task_state;
    }

    pub fn check_waiting_queue(&self) {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        let data = match data.as_mut() {
            Some(data) => data,
            None => return,
        };

        while let Some(top_task) = data.waiting_queue.peek() {
            // Priority is release_time
            if top_task.priority >= awkernel_lib::delay::uptime() {
                break; // Not executable
            }

            // Move the task from the waiting_queue to the runnable_queue.
            if let Some(mut task) = data.waiting_queue.pop() {
                self.set_task_state(&mut task.task, State::Runnable);
                let (_, absolute_deadline) = self.calculate_release_and_deadline(&task.task);
                data.runnable_queue.push(GEDFTask {
                    task: task.task.clone(),
                    priority: absolute_deadline,
                    timestamp: awkernel_lib::delay::uptime(),
                });
            }
        }
    }

    pub fn register_task(&self, task_id: u32) {
        let mut node = MCSNode::new();
        let mut ignition_counter = self.ignition_counter.lock(&mut node);
        ignition_counter.register_task(task_id);
    }

    pub fn increment_ignition(&self, task_id: u32) {
        let mut node = MCSNode::new();
        let mut ignition_counter = self.ignition_counter.lock(&mut node);
        ignition_counter.increment_ignition(task_id);
    }
}
