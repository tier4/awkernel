use crate::{delay::uptime, delta_list::DeltaList, task::Task};
use alloc::sync::Arc;
use futures::task::ArcWake;
use synctools::mcs::{MCSLock, MCSNode};

mod round_robin;

static SLEEPING: MCSLock<Sleep> = MCSLock::new(Sleep::new());

#[derive(Debug, Clone, Copy)]
pub enum SchedulerType {
    RoundRobin,
}

pub trait Scheduler {
    fn wake_task(&self, task: Arc<Task>);
    fn get_next(&self) -> Option<Arc<Task>>;
    fn scheduler_name(&self) -> SchedulerType;
}

pub fn get_next_task() -> Option<Arc<Task>> {
    if let Some(task) = round_robin::SCHEDULER.get_next() {
        return Some(task);
    }

    None
}

pub fn get_scheduler(sched_type: SchedulerType) -> &'static dyn Scheduler {
    match sched_type {
        SchedulerType::RoundRobin => &round_robin::SCHEDULER,
    }
}

struct Sleep {
    delta_list: DeltaList<Arc<Task>>,
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
    fn sleep_task(&mut self, task: Arc<Task>, mut dur: u64) {
        let now = uptime();
        if self.delta_list.is_empty() {
            self.base_time = now;
        } else {
            let diff = now - self.base_time;
            dur += diff;
        }

        self.delta_list.insert(dur, task);
    }

    fn cancel_sleep(&mut self, task_id: u64) {
        self.delta_list.filter(|t| t.get_id() != task_id);
    }

    fn wake_task(&mut self) {
        let now = uptime();

        while let Some((dur, _)) = self.delta_list.front() {
            let elapsed = now - self.base_time;
            if dur <= elapsed {
                if let DeltaList::Cons(data) = self.delta_list.pop().unwrap() {
                    let (_, task, _) = data.into_inner();
                    task.wake();
                    self.base_time += dur;
                }
            } else {
                break;
            }
        }
    }
}

/// `dur` is microseconds
pub fn sleep_task(task: Arc<Task>, dur: u64) {
    let mut node = MCSNode::new();
    let mut guard = SLEEPING.lock(&mut node);
    guard.sleep_task(task, dur);
}

pub fn cancel_sleep(task_id: u64) {
    let mut node = MCSNode::new();
    let mut guard = SLEEPING.lock(&mut node);
    guard.cancel_sleep(task_id);
}

pub fn wake_task() {
    let mut node = MCSNode::new();
    let mut guard = SLEEPING.lock(&mut node);
    guard.wake_task();
}
