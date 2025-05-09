#![no_std]
extern crate alloc;

mod parse_yaml;
mod time_unit;

use awkernel_lib::delay::wait_millisec;

pub async fn run() {
    wait_millisec(1000);
    log::info!("-- TODO: Implement the remaining DAG construction logic --");
}
