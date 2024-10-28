#![no_std]

extern crate alloc;

use alloc::sync::Arc;
use awkernel_async_lib::{scheduler::SchedulerType, spawn, sync};
use awkernel_lib::delay::wait_millisec;

// This test confirms that AsyncLock does not invoke a starvation.
pub async fn run() {
    wait_millisec(1000);
    log::debug!("test_async_mutex start");

    for i in 0..1000 {
        let mutex = Arc::new(sync::mutex::AsyncLock::new(0));

        for _ in 0..2 {
            let mutex = mutex.clone();
            spawn(
                "async_mutex".into(),
                async move {
                    let mut guard = mutex.lock().await;
                    let data = guard.as_mut();
                    *data += 1;
                    wait_millisec(10);
                },
                SchedulerType::FIFO,
            )
            .await;
        }

        wait_millisec(500);

        let guard = mutex.lock().await;
        if guard.as_ref() != &2 {
            log::debug!("starvation!!");
        }

        if i % 10 == 0 {
            log::debug!("test {i}");
        }
    }

    log::debug!("test_async_mutex end");
}
