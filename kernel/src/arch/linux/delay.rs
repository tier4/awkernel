use crate::arch::Delay;

pub struct ArchDelay;

impl Delay for ArchDelay {
    fn wait_interrupt() {}
}
