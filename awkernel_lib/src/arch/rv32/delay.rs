use crate::delay::Delay;

pub(crate) struct ArchDelay;

impl Delay for ArchDelay {
    fn wait_interrupt() {
        todo!()
    }

    fn wait_microsec(_usec: u64) {
        todo!()
    }

    fn uptime() -> u64 {
        todo!()
    }

    fn cpu_counter() -> u64 {
        todo!()
    }
}
