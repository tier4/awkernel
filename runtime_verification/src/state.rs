#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum State {
    Uninitialized,
    Ready,
    Runnable,
    Running,
    Waiting,
    Preempted,
    Terminated,
    Panicked,
}

impl core::fmt::Display for State {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Self::Uninitialized => write!(f, "Uninitialized"),
            Self::Ready => write!(f, "Ready"),
            Self::Runnable => write!(f, "Runnable"),
            Self::Running => write!(f, "Running"),
            Self::Waiting => write!(f, "Waiting"),
            Self::Preempted => write!(f, "Preempted"),
            Self::Terminated => write!(f, "Terminated"),
            Self::Panicked => write!(f, "Panicked"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct TaskState {
    pub(crate) state: State,
    pub(crate) need_sched: bool,
    pub(crate) need_preemption: bool,
}

impl core::fmt::Display for TaskState {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(
            f,
            "{}({},{})",
            self.state, self.need_sched, self.need_preemption
        )
    }
}
