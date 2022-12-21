pub use crate::arch::ArchDelay;

impl ArchDelay where ArchDelay: Delay {}

pub trait Delay {
    fn wait_interrupt();

    fn wait_microsec(usec: u32);

    fn wait_forever() -> ! {
        loop {
            Self::wait_interrupt();
        }
    }
}
