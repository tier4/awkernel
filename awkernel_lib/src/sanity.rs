use crate::{interrupt, timer};

pub fn check() {
    interrupt::sanity_check();
    timer::sanity_check();
}
