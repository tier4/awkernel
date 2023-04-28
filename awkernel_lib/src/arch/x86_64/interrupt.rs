use crate::interrupt::Interrupt;

pub struct ArchInterrupt;

impl Interrupt for ArchInterrupt {
    fn get_flag() -> usize {
        todo!()
    }

    fn disable() {
        todo!()
    }

    fn set_flag(flag: usize) {
        todo!()
    }
}
