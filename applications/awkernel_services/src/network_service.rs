use core::{future::Future, task::Poll};

use awkernel_async_lib::task::TaskResult;

pub async fn run() -> TaskResult {
    log::info!("Start {}.", crate::NETWORK_SERIVICE_NAME);

    loop {
        // Handle network interrupts
        awkernel_lib::net::network_interrupt_service();

        awkernel_async_lib::r#yield().await;

        // Wait interrupts
        NetworkService.await;
    }
}

struct NetworkService;

impl Future for NetworkService {
    type Output = ();

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        awkernel_lib::net::register_network_interrupt_service_waker(cx.waker().clone());

        if awkernel_lib::net::has_pending_irqs() {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}
