#![no_std]

extern crate alloc;

mod network_service;

use core::time::Duration;

const NETWORK_SERVICE_NAME: &str = "network service";

pub async fn run() {
    awkernel_async_lib::task::spawn(
        NETWORK_SERVICE_NAME.into(),
        network_service::run(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    );

    awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    awkernel_shell::init();
}
