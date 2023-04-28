pub(super) mod delay;
pub(super) mod interrupt;

pub fn init() {
    delay::init();
}
