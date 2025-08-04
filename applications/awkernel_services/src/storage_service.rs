use core::{future::Future, task::Poll};

use alloc::{collections::BTreeMap, format};
use awkernel_async_lib::{
    future::FutureExt, pubsub, scheduler::SchedulerType, select_biased, session_types::*,
};

const STORAGE_SERVICE_RENDEZVOUS: &str = "/awkernel/storage_service";

type ProtoInterruptHandler = Recv<(), Send<(), Eps>>;
type ChanProtoInterruptHandlerDual = Chan<(), <ProtoInterruptHandler as HasDual>::Dual>;

pub async fn run() {
    log::info!("Starting {}.", crate::STORAGE_SERVICE_NAME);

    let mut ch_irq_handlers = BTreeMap::new();

    for storage_status in awkernel_lib::storage::get_all_storage_devices() {
        log::info!("Initializing interrupt handlers for {}.", storage_status.device_name);
        spawn_handlers(storage_status, &mut ch_irq_handlers).await;
    }

    let subscriber = pubsub::create_subscriber::<(&'static str, u64)>(
        STORAGE_SERVICE_RENDEZVOUS.into(),
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
            // Storage devices don't support runtime up/down like network devices
            // Following the OpenBSD model: storage devices are operational once attached
            ("up", _id) | ("down", _id) => {
                log::warn!("Storage devices don't support runtime up/down operations");
            }
            _ => (),
        }
    }
}

async fn spawn_handlers(
    storage_status: awkernel_lib::storage::StorageStatus,
    ch_irq_handlers: &mut BTreeMap<u16, ChanProtoInterruptHandlerDual>,
) {
    for irq in storage_status.irqs {
        let (server, client) = session_channel::<ProtoInterruptHandler>();
        ch_irq_handlers.insert(irq, client);

        let name = format!(
            "{}:{}: IRQ = {irq}",
            crate::STORAGE_SERVICE_NAME,
            storage_status.device_name,
        );

        awkernel_async_lib::spawn(
            name.into(),
            interrupt_handler(storage_status.interface_id, irq, server),
            SchedulerType::FIFO,
        )
        .await;
    }
}

// Interrupt handlers.

struct StorageInterrupt {
    irq: u16,
    wait: bool,
}

impl Future for StorageInterrupt {
    type Output = ();

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let m = self.get_mut();

        if !m.wait {
            return Poll::Ready(());
        }

        m.wait = false;

        if awkernel_lib::storage::register_waker_for_storage_interrupt(m.irq, cx.waker().clone()) {
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

async fn interrupt_handler(interface_id: u64, irq: u16, ch: Chan<(), ProtoInterruptHandler>) {
    let mut ch = ch.recv().boxed().fuse();

    loop {
        let mut empty = async {}.boxed().fuse();

        select_biased! {
            (ch, _) = ch => {
                let ch = ch.send(()).await;
                ch.close();
                return;
            },
            _ = empty => {},
        }

        if awkernel_lib::storage::handle_storage_interrupt(interface_id, irq) {
            awkernel_async_lib::r#yield().await;
            continue;
        }

        // Wait interrupts.
        let mut irq_wait = StorageInterrupt { irq, wait: true }.fuse();

        select_biased! {
            (ch, _) = ch => {
                let ch = ch.send(()).await;
                ch.close();
                return;
            },
            _ = irq_wait => {},
        }

        awkernel_lib::storage::handle_storage_interrupt(interface_id, irq);
        awkernel_async_lib::r#yield().await;
    }
}