use crate::{cpu, interrupt, timer};

pub fn check() {
    cpu::sanity_check();
    interrupt::sanity_check();
    timer::sanity_check();
}
