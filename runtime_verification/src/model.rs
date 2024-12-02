use super::{
    event::Event,
    state::{State, TaskState},
};

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
        let id = self.id;
        let current = &mut self.current_state;

        let (runtime_state, runtime_need_sched, runtime_need_preemption) =
            (runtime.state, runtime.need_sched, runtime.need_preemption);

        log::debug!("[RV] id: {id}, current: {current}, event: {event}");
        match (
            current.state,
            current.need_sched,
            current.need_preemption,
            event,
        ) {
            (State::Running, true, false, Event::SetNeedPreemption) => {
                current.state = State::Running;
                current.need_sched = true;
                current.need_preemption = true;
            }
            (State::Running, true, true, Event::PollPending) => {
                current.state = State::Waiting;
                current.need_sched = false;
                current.need_preemption = true;
            }
            (State::Running, false, true, Event::SetNeedPreemption) => {
                current.state = State::Running;
                current.need_sched = false;
                current.need_preemption = true;
            }
            (State::Runnable, false, true, Event::GetNext) => {
                current.state = State::Running;
                current.need_sched = false;
                current.need_preemption = true;
            }
            (State::Waiting, false, true, Event::Wake) => {
                current.state = State::Runnable;
                current.need_sched = false;
                current.need_preemption = true;
            }
            (State::Running, false, true, Event::PollPending) => {
                current.state = State::Waiting;
                current.need_sched = false;
                current.need_preemption = true;
            }
            (State::Running, true, true, Event::PreemptionStart) => {
                current.state = State::Running;
                current.need_sched = true;
                current.need_preemption = false;
            }
            (State::Running, false, true, Event::Wake) => {
                current.state = State::Running;
                current.need_sched = true;
                current.need_preemption = true;
            }
            (State::Preempted, true, false, Event::GetNext) => {
                current.state = State::Running;
                current.need_sched = true;
                current.need_preemption = false;
            }
            (State::Running, true, false, Event::SetPreempted) => {
                current.state = State::Preempted;
                current.need_sched = true;
                current.need_preemption = false;
            }
            (State::Running, true, false, Event::PollPending) => {
                current.state = State::Waiting;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Running, false, false, Event::Wake) => {
                current.state = State::Running;
                current.need_sched = true;
                current.need_preemption = false;
            }
            (State::Preempted, false, false, Event::GetNext) => {
                current.state = State::Running;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Running, false, false, Event::SetPreempted) => {
                current.state = State::Preempted;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Running, false, false, Event::PollReady) => {
                current.state = State::Terminated;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Running, false, true, Event::PreemptionStart) => {
                current.state = State::Running;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Running, false, false, Event::SetNeedPreemption) => {
                current.state = State::Running;
                current.need_sched = false;
                current.need_preemption = true;
            }
            (State::Waiting, false, false, Event::Wake) => {
                current.state = State::Runnable;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Running, false, false, Event::PollPending) => {
                current.state = State::Waiting;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Runnable, false, false, Event::GetNext) => {
                current.state = State::Running;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Ready, false, false, Event::Wake) => {
                current.state = State::Runnable;
                current.need_sched = false;
                current.need_preemption = false;
            }
            (State::Uninitialized, false, false, Event::Spawn) => {
                current.state = State::Ready;
                current.need_sched = false;
                current.need_preemption = false;
            }
            _ => {
                let (model_state, model_need_sched, model_need_preemption) =
                    (current.state, current.need_sched, current.need_preemption);
                log::debug!(
                    "[RV ERROR] Unknown Transition Found: id: {id}, current(impl): {runtime_state}, current(model): {model_state}, event: {event}, need_sched(impl): {runtime_need_sched}, need_sched(model): {model_need_sched}, need_preemption(impl): {runtime_need_preemption}, need_preemption(model): {model_need_preemption}"
                );
            }
        }

        if current != runtime {
            let (model_state, model_need_sched, model_need_preemption) =
                (current.state, current.need_sched, current.need_preemption);
            log::debug!(
                "[RV ERROR] State Mismatch Detected: id: {id}, current(impl): {runtime_state}, current(model): {model_state}, event: {event}, need_sched(impl): {runtime_need_sched}, need_sched(model): {model_need_sched}, need_preemption(impl): {runtime_need_preemption}, need_preemption(model): {model_need_preemption}"
            );
        }
    }
}
