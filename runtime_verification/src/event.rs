#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Event {
    Spawn,
    Wake,
    GetNext,
    SetPreempted,
    PollPending,
    PollReady,
    Panic,
    SetNeedPreemption,
    PreemptionStart,
}

impl core::fmt::Display for Event {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Self::Spawn => write!(f, "Spawn"),
            Self::Wake => write!(f, "Wake"),
            Self::GetNext => write!(f, "GetNext"),
            Self::SetPreempted => write!(f, "SetPreempted"),
            Self::PollPending => write!(f, "PollPending"),
            Self::PollReady => write!(f, "PollReady"),
            Self::Panic => write!(f, "Panic"),
            Self::SetNeedPreemption => write!(f, "SetNeedPreemption"),
            Self::PreemptionStart => write!(f, "PreemptionStart"),
        }
    }
}
