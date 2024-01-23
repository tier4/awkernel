use core::{future::Future, task::Poll};

use alloc::{collections::BTreeMap, format};
use awkernel_async_lib::{
    future::FutureExt, pubsub, scheduler::SchedulerType, select_biased, session_types::*,
    task::TaskResult,
};

const NETWORK_SERVICE_RENDEZVOUS: &str = "/awkernel/network_service";

type ProtoInterruptHandler = Recv<(), Send<(), Eps>>;
type ChanProtoInterruptHandlerDual = Chan<(), <ProtoInterruptHandler as HasDual>::Dual>;

pub async fn run() -> TaskResult {
    log::info!("Starting {}.", crate::NETWORK_SERVICE_NAME);

    let mut ch_irq_handlers = BTreeMap::new();

    for if_status in awkernel_lib::net::get_all_interface() {
        if awkernel_lib::net::up(if_status.interface_id).is_ok() {
            spawn_interrupt_handler(if_status, &mut ch_irq_handlers).await;
        }
    }

    let subscriber = pubsub::create_subscriber::<(&'static str, u64)>(
        NETWORK_SERVICE_RENDEZVOUS.into(),
        pubsub::Attribute {
            queue_size: 8,
            flow_control: true,
            transient_local: false,
            lifespan: pubsub::Lifespan::Permanent,
        },
    )
    .unwrap();

    loop {
        let data = subscriber.recv().await;

        match data.data {
            ("up", id) => {
                let Ok(if_status) = awkernel_lib::net::get_interface(id) else {
                    continue;
                };

                let Ok(_) = awkernel_lib::net::up(id) else {
                    continue;
                };

                spawn_interrupt_handler(if_status, &mut ch_irq_handlers).await;
            }
            ("down", id) => {
                let Ok(if_status) = awkernel_lib::net::get_interface(id) else {
                    continue;
                };

                let Ok(_) = awkernel_lib::net::down(id) else {
                    continue;
                };

                for irq in if_status.irqs {
                    if let Some(ch) = ch_irq_handlers.remove(&irq) {
                        let ch = ch.send(()).await;
                        let (ch, _) = ch.recv().await;
                        ch.close();
                    }
                }
            }
            _ => (),
        }
    }
}

async fn spawn_interrupt_handler(
    if_status: awkernel_lib::net::IfStatus,
    ch_irq_handlers: &mut BTreeMap<u16, ChanProtoInterruptHandlerDual>,
) {
    for irq in if_status.irqs {
        let (server, client) = session_channel::<ProtoInterruptHandler>();
        ch_irq_handlers.insert(irq, client);

        let name = format!(
            "{}: device = {}, IRQ = {irq}",
            crate::NETWORK_SERVICE_NAME,
            if_status.device_name,
        );

        awkernel_async_lib::spawn(
            name.into(),
            interrupt_handler(if_status.interface_id, irq, server),
            SchedulerType::FIFO,
        )
        .await;
    }
}

struct NetworkInterrupt {
    irq: u16,
}

impl Future for NetworkInterrupt {
    type Output = ();

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        if awkernel_lib::net::register_waker_for_network_interrupt(self.irq, cx.waker().clone()) {
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

async fn interrupt_handler(interface_id: u64, irq: u16, ch: Chan<(), ProtoInterruptHandler>) {
    let mut ch = ch.recv().boxed().fuse();

    loop {
        let mut future = NetworkInterrupt { irq }.fuse();

        select_biased! {
            (ch, _) = ch => {
                let ch = ch.send(()).await;
                ch.close();
                return;
            },
            _ = future => {
                awkernel_lib::net::handle_interrupt(interface_id, irq);
            },
        }
    }
}
