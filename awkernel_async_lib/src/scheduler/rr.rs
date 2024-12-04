//! A basic RR scheduler

use super::{Scheduler, SchedulerType, Task};
use crate::task::{get_last_executed_by_task_id, set_need_preemption, State};
use alloc::{collections::vec_deque::VecDeque, sync::Arc};
use awkernel_lib::delay::uptime_nano;
use awkernel_lib::net::if_net::get_and_update_received_port;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use awkernel_lib::time_eval::{TimeEval, EVAL_COUNT};

pub struct RRScheduler {
    // Time quantum
    interval: u64,

    // Priority of this scheduler
    priority: u8,

    // Run queue
    queue: Mutex<Option<VecDeque<Arc<Task>>>>,
}

static START: Mutex<u128> = Mutex::new(0);
static WAKE_TO_GET_NEXT: TimeEval = TimeEval::new();

impl Scheduler for RRScheduler {
    fn wake_task(&self, task: Arc<Task>) {
        let mut node = MCSNode::new();
        let mut guard = self.queue.lock(&mut node);
        let mut flag = false;
        if task.id == 92 {
            flag = true;
        }
        guard.get_or_insert_with(VecDeque::new).push_back(task);
        if flag {
            let mut node = MCSNode::new();
            let mut start = START.lock(&mut node);
            if *start != 0 {
                log::info!("warning start called two times in a row");
            }
            *start = uptime_nano();
            let queue = guard.as_ref(); //.unwrap();
            let mut taskids = alloc::vec::Vec::new();
            for task in queue.as_ref().unwrap() {
                taskids.push(task.id);
            }
            if *start % 10000 == 0 {
                log::info!("taskids:{:?}", taskids);
            }
        }
    }

    fn get_next(&self) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut guard = self.queue.lock(&mut node);

        let queue = match guard.as_mut() {
            Some(d) => d,
            None => return None,
        };

        //let port = get_and_update_received_port();
        let port = 0;

        let index;
        if port == 0 {
            index = 0;
        } else {
            let task_id = (port + 44) as u32;
            index = queue
                .iter()
                .position(|task| task.id == task_id)
                .unwrap_or(0);
        }

        //while let Some(task) = queue.pop_front() {
        while let Some(task) = queue.remove(index) {
            {
                let mut node = MCSNode::new();
                let mut task_info = task.info.lock(&mut node);

                if matches!(task_info.state, State::Terminated | State::Panicked) {
                    continue;
                }

                task_info.state = State::Running;
            }

            if task.id == 92 {
                let end = uptime_nano();
                let mut node = MCSNode::new();
                let mut start = START.lock(&mut node);
                let count = WAKE_TO_GET_NEXT.add(end - *start);
                *start = 0;
                if count % EVAL_COUNT == 0 {
                    log::debug!("Average time: {} ns", WAKE_TO_GET_NEXT.average());
                    WAKE_TO_GET_NEXT.reset();
                }
            }

            return Some(task);
        }

        None
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::RR
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

pub static SCHEDULER: RRScheduler = RRScheduler {
    // Time quantum (20 ms)
    interval: 20_000,

    // TODO: Temporarily set to the lowest priority
    priority: 16,

    queue: Mutex::new(None),
};

impl RRScheduler {
    // Invoke a preemption if the task exceeds the time quantum
    pub fn invoke_preemption(&self, cpu_id: usize, task_id: u32) {
        let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
        if let Some(last_executed) = get_last_executed_by_task_id(task_id) {
            let elapsed = awkernel_lib::delay::uptime() - last_executed;
            if last_executed != 0 && elapsed > self.interval {
                set_need_preemption(task_id);
                awkernel_lib::interrupt::send_ipi(preempt_irq, cpu_id as u32);
            }
        }
    }
}
