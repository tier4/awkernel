//! A prioritized LIFO scheduler.

use core::cmp::max;

use super::{Scheduler, SchedulerType, Task};
use crate::scheduler::{peek_preemption_pending, push_preemption_pending, GLOBAL_WAKE_GET_MUTEX};
use crate::task::{get_task, get_tasks_running, set_current_task, set_need_preemption};
use crate::{scheduler::get_priority, task::State};
use alloc::collections::VecDeque;
use alloc::sync::Arc;
use alloc::vec::Vec;
use array_macro::array;
use awkernel_lib::priority_queue::HIGHEST_PRIORITY;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub struct PrioritizedLIFOScheduler {
    data: Mutex<Option<PrioritizedLIFOData>>, // Run queue.
    priority: u8,
}

struct PrioritizedLIFOTask {
    task: Arc<Task>,
    _priority: u8,
}

struct PrioritizedLIFOData {
    queues: [VecDeque<PrioritizedLIFOTask>; HIGHEST_PRIORITY as usize + 1],
    has_entry: u32,
}
