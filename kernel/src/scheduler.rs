use crate::task::Task;
use alloc::sync::Arc;

mod round_robin;

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
