use super::{event::Event, model::Model};
use alloc::vec;

static TRUE: Option<bool> = Some(true);
static FALSE: Option<bool> = Some(false);
static DC: Option<bool> = None;

type NeedSched = Option<bool>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskModelState {
    NotExisting(NeedSched),
    Ready(NeedSched),
    Running(NeedSched),
    Runnable(NeedSched),
    Waiting(NeedSched),
    Preempted(NeedSched),
    Terminated(NeedSched),
    Panicked(NeedSched),
}

impl core::fmt::Display for TaskModelState {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Self::NotExisting(_) => write!(f, "NotExisting"),
            Self::Ready(Some(need_sched)) => write!(f, "Ready({})", need_sched),
            Self::Running(Some(need_sched)) => write!(f, "Running({})", need_sched),
            Self::Runnable(Some(need_sched)) => write!(f, "Runnable({})", need_sched),
            Self::Waiting(Some(need_sched)) => write!(f, "Waiting({})", need_sched),
            Self::Preempted(Some(need_sched)) => write!(f, "Preempted({})", need_sched),
            Self::Terminated(_) => write!(f, "Terminated"),
            Self::Panicked(_) => write!(f, "Panicked"),
            _ => core::unreachable!(),
        }
    }
}

pub type TaskModel = Model<TaskModelState, Event>;

pub fn new_task_model() -> Model<TaskModelState, Event> {
    use super::{event::Event::*, task::TaskModelState::*};
    let initial_state = NotExisting(DC);
    let transitions = vec![
        (NotExisting(DC), Spawn, Ready(FALSE)),
        (Ready(FALSE), Wake, Runnable(FALSE)),
        (Runnable(FALSE), GetNext, Running(FALSE)),
        (Running(FALSE), PollReady, Terminated(DC)),
        (Running(FALSE), Panic, Panicked(DC)),
        (Running(TRUE), PollReady, Terminated(DC)),
        (Running(TRUE), Panic, Panicked(DC)),
        (Running(FALSE), SetNeedSched, Running(TRUE)),
        (Running(FALSE), Wake, Running(TRUE)),
        (Running(TRUE), PollPending, Waiting(TRUE)),
        (Waiting(TRUE), Wake, Runnable(TRUE)),
        (Running(TRUE), Preempt, Preempted(TRUE)),
        (Preempted(TRUE), GetNext, Running(FALSE)),
        (Running(FALSE), Preempt, Running(FALSE)),
        (Running(FALSE), PollPending, Waiting(FALSE)),
        (Waiting(FALSE), Wake, Runnable(FALSE)),
        (Runnable(TRUE), GetNext, Running(FALSE)),
        (Running(FALSE), GetNext, Running(FALSE)),
    ];

    let states = vec![
        NotExisting(DC),
        Ready(FALSE),
        Running(FALSE),
        Running(TRUE),
        Runnable(FALSE),
        Runnable(TRUE),
        Waiting(FALSE),
        Waiting(TRUE),
        Preempted(TRUE),
        Terminated(DC),
        Panicked(DC),
    ];

    Model::new(initial_state, states, transitions)
}
