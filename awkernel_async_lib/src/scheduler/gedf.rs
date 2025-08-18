//! A GEDF scheduler.

use super::{Scheduler, SchedulerType, Task};
use crate::{
    dag::{get_dag_absolute_deadline, set_dag_absolute_deadline},
    scheduler::get_priority,
    task::{get_absolute_deadline_by_task_id, get_dag_id_by_task_id, get_tasks_running, set_need_preemption, State, task_belongs_to_dag},
};
use alloc::{collections::BinaryHeap, sync::Arc};
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
        let mut data = self.data.lock(&mut node);
        let data = data.get_or_insert_with(GEDFData::new);

        let mut node = MCSNode::new();
        let mut info = task.info.lock(&mut node);

        let SchedulerType::GEDF(relative_deadline) = info.scheduler_type else {
            unreachable!();
        };

        let wake_time = awkernel_lib::delay::uptime();
        let absolute_deadline ;
        // DAGに所属している場合
        if let Some(dag_id) = get_dag_id_by_task_id(task.id) {//ここでnode_indexを持ってくる
            // DAGの絶対デッドラインを取得
            if let Some(dag_absolute_deadline) = get_dag_absolute_deadline(dag_id) {//今持ってきたnode_indexのidとソースノードのidを比較
                //ではない→if letでDAGの絶対デッドラインを取得
                //if letのelseはunreachable!()でエラーを出す
                //ソースノードだった場合：所属しているDAGのsink_nodeの相対デッドライン(DAGの相対デッドライン)を取得→wake+relativeで絶対デッドラインを計算
                //けいさんしたものをDAGの絶対デッドラインとして更新→キューに入れる

                // DAGの絶対デッドラインが既に設定されている場合、それを使用
                absolute_deadline = dag_absolute_deadline;
            } else {//周期ごとにdlがかわる→DAGの最初のノードが起き始めた時(wake)が更新タイミング→relativeを足す(101行目)
                // DAGの絶対デッドラインが未設定の場合、NodeInfoからrelative_deadlineを取得して計算
                // if let Some(relative_deadline) = get_relative_deadline_by_task_id(task.id) {
                //     let relative_deadline_ms = relative_deadline.as_millis() as u64;
                //     absolute_deadline = wake_time + relative_deadline_ms;
                //     set_dag_absolute_deadline(dag_id, absolute_deadline);
                // } else {
                //     // NodeInfoからrelative_deadlineが取得できない場合（エラーケース）
                //     // スケジューラータイプから取得したrelative_deadlineを使用
                //     let SchedulerType::GEDF(relative_deadline) = info.scheduler_type else {
                //         unreachable!();
                //     };
                //     absolute_deadline = wake_time + relative_deadline;
                //     set_dag_absolute_deadline(dag_id, absolute_deadline);
                // }
                absolute_deadline = 0;
            }
        } else {
            // DAGに所属していない単一タスクの場合
            absolute_deadline = 0;
        }

        task.priority
            .update_priority_info(self.priority, absolute_deadline);
        info.update_absolute_deadline(absolute_deadline);

        data.queue.push(GEDFTask {
            task: task.clone(),
            absolute_deadline,
            wake_time,
        });

        self.invoke_preemption(absolute_deadline);
    }

    fn get_next(&self) -> Option<Arc<Task>> {
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
                task_info.state = State::Running;
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
    fn invoke_preemption(&self, absolute_deadline: u64) {
        // Get running tasks and filter out tasks with task_id == 0.
        let mut tasks = get_tasks_running();
        tasks.retain(|task| task.task_id != 0);

        // If the number of running tasks is less than the number of non-primary CPUs, preempt is not required.
        let num_non_primary_cpus = num_cpu() - 1;
        if tasks.len() < num_non_primary_cpus {
            return;
        }

        let task_with_max_deadline = tasks
            .iter()
            .filter_map(|task| {
                get_absolute_deadline_by_task_id(task.task_id).map(|deadline| (task, deadline))
            })
            .max_by_key(|&(_, deadline)| deadline);

        if let Some((task, max_absolute_deadline)) = task_with_max_deadline {
            if max_absolute_deadline > absolute_deadline {
                let preempt_irq = awkernel_lib::interrupt::get_preempt_irq();
                set_need_preemption(task.task_id, task.cpu_id);
                awkernel_lib::interrupt::send_ipi(preempt_irq, task.cpu_id as u32);
            }
        }
    }
}
