use super::{
    event::Event,
    state::{State, TaskState},
};
use alloc::collections::btree_map::BTreeMap;
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

pub static COUNTER: Mutex<BTreeMap<(State, bool, bool, Event), usize>> =
    Mutex::new(BTreeMap::new());

pub struct TaskModel {
    id: u32,
    current_state: TaskState,
}

impl TaskModel {
    pub fn new(id: u32) -> Self {
        Self {
            id,
            current_state: TaskState {
                state: State::Uninitialized,
                need_sched: false,
                need_preemption: false,
            },
        }
    }
    pub fn transition(&mut self, event: &Event, runtime: &TaskState) {
        let cpu_id = awkernel_lib::cpu::cpu_id();
        let id = self.id;
        let prev = self.current_state.clone();
        let current = &mut self.current_state;

        let (runtime_state, runtime_need_sched, runtime_need_preemption) =
            (runtime.state, runtime.need_sched, runtime.need_preemption);

        let key = (
            current.state,
            current.need_sched,
            current.need_preemption,
            *event,
        );

        let mut node = MCSNode::new();
        let mut counter = COUNTER.lock(&mut node);

        match key.clone() {
            (State::Running, true, false, Event::SetNeedPreemption) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Running;
                current.need_sched = true;
                current.need_preemption = true;
            }
            (State::Running, true, true, Event::PollPending) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Waiting;
                current.need_sched = false;
                current.need_preemption = true;
            }
            (State::Running, false, true, Event::SetNeedPreemption) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Running;
                current.need_sched = false;
                current.need_preemption = true;
            }
            (State::Runnable, false, true, Event::GetNext) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Running;
                current.need_sched = false;
                current.need_preemption = true;
            }
            (State::Waiting, false, true, Event::Wake) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Runnable;
                current.need_sched = false;
                current.need_preemption = true;
            }
            (State::Running, false, true, Event::PollPending) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Waiting;
                current.need_sched = false;
                current.need_preemption = true;
            }
            (State::Running, true, true, Event::PreemptionStart) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Running;
                current.need_sched = true;
                current.need_preemption = false;
            }
            (State::Running, false, true, Event::Wake) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Running;
                current.need_sched = true;
                current.need_preemption = true;
            }
            (State::Preempted, true, false, Event::GetNext) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Running;
                current.need_sched = true;
                current.need_preemption = false;
            }
            (State::Running, true, false, Event::SetPreempted) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Preempted;
                current.need_sched = true;
                current.need_preemption = false;
            }
            (State::Running, true, false, Event::PollPending) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Waiting;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Running, false, false, Event::Wake) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Running;
                current.need_sched = true;
                current.need_preemption = false;
            }
            (State::Preempted, false, false, Event::GetNext) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Running;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Running, false, false, Event::SetPreempted) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Preempted;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Running, false, false, Event::PollReady) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Terminated;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Running, false, true, Event::PreemptionStart) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Running;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Running, false, false, Event::SetNeedPreemption) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Running;
                current.need_sched = false;
                current.need_preemption = true;
            }
            (State::Waiting, false, false, Event::Wake) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Runnable;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Running, false, false, Event::PollPending) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Waiting;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Runnable, false, false, Event::GetNext) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Running;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Ready, false, false, Event::Wake) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Runnable;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Uninitialized, false, false, Event::Spawn) => {
                *counter.entry(key).or_insert(0) += 1;
                current.state = State::Ready;
                current.need_sched = false;
                current.need_preemption = false;
            }
            _ => {
                let (model_state, model_need_sched, model_need_preemption) =
                    (current.state, current.need_sched, current.need_preemption);
                log::debug!(
                    "[RV ERROR] Unknown Transition Found: cpu id: {cpu_id}, task id: {id}, current(impl): {runtime_state}, current(model): {model_state}, event: {event}, need_sched(impl): {runtime_need_sched}, need_sched(model): {model_need_sched}, need_preemption(impl): {runtime_need_preemption}, need_preemption(model): {model_need_preemption}"
                );
            }
        }

        if current != runtime {
            let (model_state, model_need_sched, model_need_preemption) =
                (current.state, current.need_sched, current.need_preemption);
            log::debug!(
                "[RV ERROR] State Mismatch Detected: cpu id: {cpu_id}, task id: {id}, current(impl): {runtime_state}, current(model): {model_state}, event: {event}, need_sched(impl): {runtime_need_sched}, need_sched(model): {model_need_sched}, need_preemption(impl): {runtime_need_preemption}, need_preemption(model): {model_need_preemption}"
            );
        }

        log::debug!("[RV] cpu id: {cpu_id}, task id: {id}, current: {prev}, event: {event}, next: {current}");
        for ((state, need_sched, need_preemption, event), count) in counter.iter() {
            log::debug!(
                "[RV counter] state: {state}, need_sched: {need_sched}, need_preemption: {need_preemption}, event: {event}, count: {count}"
            );
        }
    }
}
