#![no_std]

extern crate alloc;

use alloc::sync::Arc;
use awkernel_async_lib::{scheduler::SchedulerType, spawn, sync};
use awkernel_lib::delay::wait_millisec;

/// This test confirms that
pub async fn run() {
    wait_millisec(1000);
    log::debug!("test_async_mutex");

    let mutex = Arc::new(sync::mutex::AsyncLock::new(0));

    for _i in 1..10000 {
        let mutex = mutex.clone();
        spawn(
            "async_mutex".into(),
            async move {
                let mut guard = mutex.lock().await;
                let data = guard.as_mut();
                *data += 1;
            },
            SchedulerType::FIFO,
        )
        .await;
    }

    wait_millisec(1000);

    let guard = mutex.lock().await;
    log::debug!("data = {}", guard.as_ref());
}
