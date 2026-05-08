#![no_std]

extern crate alloc;

mod buffered_logger;
mod network_service;

use core::time::Duration;

const NETWORK_SERVICE_NAME: &str = "[Awkernel] network service";
const BUFFERED_LOGGER_NAME: &str = "[Awkernel] buffered logger service";
const DISPLAY_SERVICE_NAME: &str = "[Awkernel] display service";
const WATCHDOG_NAME: &str = "[Awkernel] watchdog";

/// Auto-reboot after this many seconds. Set to 0 to disable.
const WATCHDOG_REBOOT_SECS: u64 = 60;

pub async fn run() {
    awkernel_async_lib::spawn(
        BUFFERED_LOGGER_NAME.into(),
        buffered_logger::run(),
        awkernel_async_lib::scheduler::SchedulerType::PrioritizedFIFO(0),
    )
    .await;

    awkernel_async_lib::spawn(
        NETWORK_SERVICE_NAME.into(),
        network_service::run(),
        awkernel_async_lib::scheduler::SchedulerType::PrioritizedFIFO(0),
    )
    .await;

    awkernel_async_lib::spawn(
        DISPLAY_SERVICE_NAME.into(),
        awkernel_display::run(),
        awkernel_async_lib::scheduler::SchedulerType::PrioritizedFIFO(0),
    )
    .await;

    if WATCHDOG_REBOOT_SECS > 0 {
        awkernel_async_lib::spawn(
            WATCHDOG_NAME.into(),
            watchdog_reboot(WATCHDOG_REBOOT_SECS),
            awkernel_async_lib::scheduler::SchedulerType::PrioritizedFIFO(0),
        )
        .await;
    }

    awkernel_async_lib::sleep(Duration::from_secs(1)).await;
    awkernel_shell::init();
}

/// Sleep for the given number of seconds and then reboot.
async fn watchdog_reboot(secs: u64) {
    log::info!("Watchdog: will reboot in {secs} seconds");
    awkernel_async_lib::sleep(Duration::from_secs(secs)).await;
    log::info!("Watchdog: rebooting now after {secs} seconds");

    #[cfg(target_arch = "x86_64")]
    awkernel_lib::arch::x86_64::power::reboot();
}
