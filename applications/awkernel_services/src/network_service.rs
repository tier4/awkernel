use core::{future::Future, task::Poll, time::Duration};

use alloc::{collections::BTreeMap, format};
use awkernel_async_lib::{
    future::FutureExt, pubsub, scheduler::SchedulerType, select_biased, session_types::*,
};

const NETWORK_SERVICE_RENDEZVOUS: &str = "/awkernel/network_service";

const GARBAGE_COLLECTOR_NAME: &str = "[Awkernel] TCP garbage collector";

type ProtoInterruptHandler = Recv<(), Send<(), Eps>>;
type ChanProtoInterruptHandlerDual = Chan<(), <ProtoInterruptHandler as HasDual>::Dual>;

pub async fn run() {
    log::info!("Starting {}.", crate::NETWORK_SERVICE_NAME);

    awkernel_async_lib::spawn(
        GARBAGE_COLLECTOR_NAME.into(),
        tcp_garbage_collector(),
        SchedulerType::FIFO,
    )
    .await;

    let mut ch_irq_handlers = BTreeMap::new();
    let mut ch_poll_handlers = BTreeMap::new();
    let mut ch_tick_handlers = BTreeMap::new();

    for if_status in awkernel_lib::net::get_all_interface() {
        log::info!("Waking {} up.", if_status.device_name);
        if awkernel_lib::net::up(if_status.interface_id).is_ok() {
            spawn_handlers(
                if_status,
                &mut ch_irq_handlers,
                &mut ch_poll_handlers,
                &mut ch_tick_handlers,
            )
            .await;
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

                spawn_handlers(
                    if_status,
                    &mut ch_irq_handlers,
                    &mut ch_poll_handlers,
                    &mut ch_tick_handlers,
                )
                .await;
            }
            ("down", id) => {
                let Ok(if_status) = awkernel_lib::net::get_interface(id) else {
                    continue;
                };

                let Ok(_) = awkernel_lib::net::down(id) else {
                    continue;
                };

                // Close interrupt handlers.
                for irq in if_status.irqs {
                    if let Some(ch) = ch_irq_handlers.remove(&irq) {
                        let ch = ch.send(()).await;
                        let (ch, _) = ch.recv().await;
                        ch.close();
                    }
                }

                // Close poll handlers.
                if let Some(ch) = ch_poll_handlers.remove(&if_status.interface_id) {
                    let ch = ch.send(()).await;
                    let (ch, _) = ch.recv().await;
                    ch.close();
                }
            }
            _ => (),
        }
    }
}

async fn spawn_handlers(
    if_status: awkernel_lib::net::IfStatus,
    ch_irq_handlers: &mut BTreeMap<u16, ChanProtoInterruptHandlerDual>,
    ch_poll_handlers: &mut BTreeMap<u64, ChanProtoInterruptHandlerDual>,
    ch_tick_handlers: &mut BTreeMap<u64, ChanProtoInterruptHandlerDual>,
) {
    for irq in if_status.irqs {
        let (server, client) = session_channel::<ProtoInterruptHandler>();
        ch_irq_handlers.insert(irq, client);

        let name = format!(
            "{}:{}: IRQ = {irq}",
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

    if if_status.poll_mode {
        let (server, client) = session_channel::<ProtoInterruptHandler>();
        ch_poll_handlers.insert(if_status.interface_id, client);

        let name = format!(
            "{}:{}: poll mode",
            crate::NETWORK_SERVICE_NAME,
            if_status.device_name,
        );

        awkernel_async_lib::spawn(
            name.into(),
            poll_handler(if_status.interface_id, server),
            SchedulerType::FIFO,
        )
        .await;
    }

    if let Some(tick_msec) = if_status.tick_msec {
        let (server, client) = session_channel::<ProtoInterruptHandler>();
        ch_tick_handlers.insert(if_status.interface_id, client);

        let name = format!(
            "{}:{}: tick = {tick_msec} [msec]",
            crate::NETWORK_SERVICE_NAME,
            if_status.device_name,
        );

        awkernel_async_lib::spawn(
            name.into(),
            tick_handler(if_status.interface_id, tick_msec, server),
            SchedulerType::FIFO,
        )
        .await;
    }
}

async fn tcp_garbage_collector() {
    let dur = Duration::from_millis(100);
    loop {
        awkernel_async_lib::sleep(dur).await;
        awkernel_lib::net::tcp_stream::close_connections();
    }
}

// Interrupt handlers.

struct NetworkInterrupt {
    irq: u16,
    wait: bool,
}

impl Future for NetworkInterrupt {
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

        if awkernel_lib::net::register_waker_for_network_interrupt(m.irq, cx.waker().clone()) {
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

        if awkernel_lib::net::handle_interrupt(interface_id, irq) {
            awkernel_async_lib::r#yield().await;
            continue;
        }

        // Wait interrupts.
        let mut irq_wait = NetworkInterrupt { irq, wait: true }.fuse();

        select_biased! {
            (ch, _) = ch => {
                let ch = ch.send(()).await;
                ch.close();
                return;
            },
            _ = irq_wait => {},
        }

        awkernel_lib::net::handle_interrupt(interface_id, irq);
        awkernel_async_lib::r#yield().await;
    }
}

// Poll mode devices.

struct NetworkPoll {
    interface_id: u64,
    wait: bool,
}

impl Future for NetworkPoll {
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

        if awkernel_lib::net::register_waker_for_poll(m.interface_id, cx.waker().clone()) {
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

async fn poll_handler(interface_id: u64, ch: Chan<(), ProtoInterruptHandler>) {
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

        if awkernel_lib::net::poll_interface(interface_id) {
            awkernel_async_lib::r#yield().await;
            continue;
        }

        // Wait some events.
        let mut poll_wait = NetworkPoll {
            interface_id,
            wait: true,
        }
        .fuse();

        select_biased! {
            (ch, _) = ch => {
                let ch = ch.send(()).await;
                ch.close();
                return;
            },
            _ = poll_wait => {},
        }

        awkernel_lib::net::poll_interface(interface_id);
        awkernel_async_lib::r#yield().await;
    }
}

// Tick
async fn tick_handler(interface_id: u64, tick: u64, ch: Chan<(), ProtoInterruptHandler>) {
    let mut ch = ch.recv().boxed().fuse();

    loop {
        awkernel_lib::net::tick_interface(interface_id);

        let mut sleeper = awkernel_async_lib::sleep(Duration::from_millis(tick))
            .boxed()
            .fuse();

        select_biased! {
            (ch, _) = ch => {
                let ch = ch.send(()).await;
                ch.close();
                return;
            },
            _ = sleeper => {},
        }
    }
}
