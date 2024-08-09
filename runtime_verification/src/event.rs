#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    Spawn,
    Wake,
    GetNext,
    Preempt,
    PollPending,
    PollReady,
    Panic,
    SetNeedSched,
}

impl core::fmt::Display for Event {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Self::Wake => write!(f, "Wake"),
            Self::GetNext => write!(f, "GetNext"),
            Self::Spawn => write!(f, "Spawn"),
            Self::Preempt => write!(f, "Preempt"),
            Self::PollPending => write!(f, "PollPending"),
            Self::PollReady => write!(f, "PollReady"),
            Self::Panic => write!(f, "Panic"),
            Self::SetNeedSched => write!(f, "SetNeedSched"),
        }
    }
}
