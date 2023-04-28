use crate::interrupt::Interrupt;

pub struct ArchInterrupt;

impl Interrupt for ArchInterrupt {
    fn get_flag() -> usize {
        0
    }

    fn disable() {}

    fn enable() {}

    fn set_flag(_flag: usize) {}
}
