#![no_std]

extern crate alloc;

mod buffered_logger;
mod network_service;

use core::time::Duration;

const NETWORK_SERVICE_NAME: &str = "[Awkernel] network service";
const BUFFERED_LOGGER_NAME: &str = "[Awkernel] buffered logger service";

pub async fn run() {
    awkernel_async_lib::spawn(
        BUFFERED_LOGGER_NAME.into(),
        buffered_logger::run(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;

    awkernel_async_lib::spawn(
        NETWORK_SERVICE_NAME.into(),
        network_service::run(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;

    awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    awkernel_shell::init();
}
