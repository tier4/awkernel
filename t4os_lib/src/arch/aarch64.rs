pub(super) mod delay;

pub fn init_primary() {
    delay::init_primary();
}

pub fn init_non_primary() {
    delay::init_non_primary();
}
