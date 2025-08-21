//! A GEDF scheduler.

use core::cmp::max;

use super::{Scheduler, SchedulerType, Task};
use crate::{
    dag::{get_dag_absolute_deadline, set_dag_absolute_deadline, get_dag, to_node_index},
    scheduler::{get_priority, peek_preemption_pending, push_preemption_pending},
    task::{
        get_absolute_deadline_by_task_id, get_task, get_tasks_running, set_current_task, set_need_preemption, State, 
        get_dag_info_by_task_id, MAX_TASK_PRIORITY,
    },
};
use alloc::{collections::BinaryHeap, sync::Arc, vec::Vec};
use awkernel_lib::{
    cpu::num_cpu,
    sync::mutex::{MCSNode, Mutex},
};



pub struct GEDFScheduler {
    data: Mutex<Option<GEDFData>>, // Run queue.
    priority: u8,
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
        // The reason for acquiring this lock before invoke_preemption() is to prevent priority inversion from occurring
        // when invoke_preemption() is executed between the time the next task is determined and the RUNNING is updated
        // within the scheduler's get_next().
        let mut data = self.data.lock(&mut node);
        let internal_data = data.get_or_insert_with(GEDFData::new);

        let (wake_time, absolute_deadline) = {
            let mut node_inner = MCSNode::new();
            let mut info = task.info.lock(&mut node_inner);
            match info.scheduler_type {
                SchedulerType::GEDF(relative_deadline) => {
                    let wake_time = awkernel_lib::delay::uptime();
                    let absolute_deadline ;
                    // DAGに所属している場合
                    if let Some((dag_id, node_index)) = get_dag_info_by_task_id(task.id) {
                        // DAGを取得してソースノードかどうかを判定
                        if let Some(dag) = get_dag(dag_id) {
                            //u32-->nodeindex
                            // let current_node_index = to_node_index(node_index);
                            // let is_source_node = dag.is_source_node(current_node_index);
                        
                            // DAGの絶対デッドラインを取得
                            if let Some(dag_absolute_deadline) = get_dag_absolute_deadline(dag_id) {
                                // DAGの絶対デッドラインが既に設定されている場合、それを使用
                                absolute_deadline = dag_absolute_deadline;
                            } else {
                                // DAGの絶対デッドラインが未設定の場合（最初の周期）
                                // 最初にwakeしたノードがDAG全体の周期を決定
                                
                                // DAGのsink_nodeの相対デッドラインを取得して周期を決定
                                let sink_relative_deadline = dag.get_sink_relative_deadline();
                                
                                // sink_nodeの相対デッドラインが設定されている場合はそれを使用、
                                // そうでなければスケジューラータイプから取得→後で消去
                                let relative_deadline_ms = if let Some(deadline) = sink_relative_deadline {
                                    deadline.as_millis() as u64
                                } else {
                                    relative_deadline
                                };
                                
                                // 絶対デッドラインを計算してDAGに設定
                                absolute_deadline = wake_time + relative_deadline_ms;
                                set_dag_absolute_deadline(dag_id, absolute_deadline);
                            }
                        } else {
                            // DAGが見つからない場合（エラーケース）
                            unreachable!();
                        }
                    } else {
                        // DAGに所属していない単一タスクの場合
                        absolute_deadline = wake_time + relative_deadline;
                    }
                    task.priority
                        .update_priority_info(self.priority, MAX_TASK_PRIORITY - absolute_deadline);
                    info.update_absolute_deadline(absolute_deadline);

                    (wake_time, absolute_deadline)
                }
                _ => unreachable!(),
            }
        };
        if !self.invoke_preemption(task.clone()) {
            internal_data.queue.push(GEDFTask {
                task: task.clone(),
                absolute_deadline,
                wake_time,
            });
        }
    }

    fn get_next(&self, execution_ensured: bool) -> Option<Arc<Task>> {
        let mut node = MCSNode::new();
        let mut data = self.data.lock(&mut node);

        #[allow(clippy::question_mark)]
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

                if task_info.state == State::Preempted {
                    task_info.need_preemption = false;
                }
                if execution_ensured {
                    task_info.state = State::Running;
                    set_current_task(awkernel_lib::cpu::cpu_id(), task.task.id);
                }
            }

            return Some(task.task);
        }
    }

    fn scheduler_name(&self) -> SchedulerType {
        SchedulerType::GEDF(0)
    }

    fn priority(&self) -> u8 {
        self.priority
    }
}

pub static SCHEDULER: GEDFScheduler = GEDFScheduler {
    data: Mutex::new(None),
    priority: get_priority(SchedulerType::GEDF(0)),
};

impl GEDFScheduler {
    fn invoke_preemption(&self, task: Arc<Task>) -> bool {
        let tasks_running = get_tasks_running()
            .into_iter()
            .filter(|rt| rt.task_id != 0) // Filter out idle CPUs
            .collect::<Vec<_>>();

        // If the task has already been running, preempt is not required.
        if tasks_running.is_empty() || tasks_running.iter().any(|rt| rt.task_id == task.id) {
            return false;
        }

        let preemption_target = tasks_running
            .iter()
            .filter_map(|rt| {
                get_task(rt.task_id).map(|t| {
                    let highest_pending = peek_preemption_pending(rt.cpu_id).unwrap_or(t.clone());
                    (max(t, highest_pending), rt.cpu_id)
                })
            })
            .min()
            .unwrap();

        let (target_task, target_cpu) = preemption_target;
        if task > target_task {
            push_preemption_pending(target_cpu, task);
            let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
            set_need_preemption(target_task.id, target_cpu);
            awkernel_lib::interrupt::send_ipi(preempt_irq, target_cpu as u32);

            // NOTE(atsushi421): Currently, preemption is requested regardless of the number of idle CPUs.
            // While this implementation easily prevents priority inversion, it may also cause unnecessary preemption.
            // Therefore, a more sophisticated implementation will be considered in the future.

            return true;
        }

        false
    }
}
