use crate::interrupt::Interrupt;

impl Interrupt for super::StdCommon {
    fn get_flag() -> usize {
        0
    }

    fn disable() {}

    fn enable() {}

    fn set_flag(_flag: usize) {}
}
