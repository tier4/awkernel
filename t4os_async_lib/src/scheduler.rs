use crate::{delay::uptime, delta_list::DeltaList, task::Task};
use alloc::{boxed::Box, sync::Arc};
use synctools::mcs::{MCSLock, MCSNode};

mod round_robin;

static SLEEPING: MCSLock<Sleep> = MCSLock::new(Sleep::new());

#[derive(Debug, Clone, Copy)]
pub enum SchedulerType {
    RoundRobin,
}

pub(crate) trait Scheduler {
    /// Enqueue a executable task.
    /// The enqueued task will be take by `get_next()`.
    fn wake_task(&self, task: Arc<Task>);

    /// Get a next executable task.
    fn get_next(&self) -> Option<Arc<Task>>;

    /// Get the scheduler name.
    fn scheduler_name(&self) -> SchedulerType;
}

pub(crate) fn get_next_task() -> Option<Arc<Task>> {
    if let Some(task) = round_robin::SCHEDULER.get_next() {
        return Some(task);
    }

    None
}

pub(crate) fn get_scheduler(sched_type: SchedulerType) -> &'static dyn Scheduler {
    match sched_type {
        SchedulerType::RoundRobin => &round_robin::SCHEDULER,
    }
}

struct Sleep {
    delta_list: DeltaList<Box<dyn FnOnce() -> ()>>,
    base_time: u64,
}

impl Sleep {
    const fn new() -> Self {
        Self {
            delta_list: DeltaList::Nil,
            base_time: 0,
        }
    }

    /// `dur` is microseconds
    fn sleep_task(&mut self, handler: Box<dyn FnOnce() -> ()>, mut dur: u64) {
        let now = uptime();
        if self.delta_list.is_empty() {
            self.base_time = now;
        } else {
            let diff = now - self.base_time;
            dur += diff;
        }

        self.delta_list.insert(dur, handler);
    }

    fn wake_task(&mut self) {
        let now = uptime();

        while let Some((dur, _)) = self.delta_list.front() {
            let elapsed = now - self.base_time;
            if dur <= elapsed {
                if let DeltaList::Cons(data) = self.delta_list.pop().unwrap() {
                    let (_, handler, _) = data.into_inner();
                    handler();

                    self.base_time += dur;
                }
            } else {
                break;
            }
        }
    }
}

/// `dur` is microseconds
pub(crate) fn sleep_task(sleep_handler: Box<dyn FnOnce() -> ()>, dur: u64) {
    let mut node = MCSNode::new();
    let mut guard = SLEEPING.lock(&mut node);
    guard.sleep_task(sleep_handler, dur);
}

pub fn wake_task() {
    let mut node = MCSNode::new();
    let mut guard = SLEEPING.lock(&mut node);
    guard.wake_task();
}
