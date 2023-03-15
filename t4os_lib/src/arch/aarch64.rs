pub(super) mod delay;

pub unsafe fn init_primary() {
    delay::init_primary();
}

pub unsafe fn init_non_primary() {
    delay::init_non_primary();
}
