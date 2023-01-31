//! # Examples
//!
//! ## A Simple Protocol
//!
//! ```text
//! Client                 Server
//!    |                     |
//!    | --------------> u64 |
//!    | bool <------------- |
//!    |                     |
//!  close                 close
//! ```
//!
//! ```
//! use t4os_async_lib::{service, session_types::*, scheduler::SchedulerType};
//!
//! // Define protocol.
//! type Server = Recv<u64, Send<bool, Eps>>;
//! type Client = <Server as HasDual>::Dual;
//!
//! async fn srv(c: Chan<(), Server>) {
//!     let (c, n) = c.recv().await;
//!     let c = if n % 2 == 0 {
//!         c.send(true).await
//!     } else {
//!         c.send(false).await
//!     };
//!     c.close();
//! }
//!
//! async fn cli(c: Chan<(), Client>) {
//!     let c = c.send(9).await;
//!     let (c, result) = c.recv().await;
//!     c.close();
//! }
//!
//! async fn simple() {
//!     // Start a server.
//!     let accepter = service::create_server::<Server>("simple service".into()).unwrap();
//!
//!     // Spawn a connection accepter.
//!     t4os_async_lib::spawn(
//!         async move {
//!             while let Ok(chan) = accepter.accept().await {
//!                 // Spawn a task for the connection.
//!                 t4os_async_lib::spawn(
//!                     async move {
//!                         srv(chan).await;
//!                     },
//!                     SchedulerType::RoundRobin,
//!                 ).await;
//!             }
//!         },
//!         SchedulerType::RoundRobin,
//!     ).await;
//!
//!     // Start a client.
//!     t4os_async_lib::spawn(
//!         async {
//!             let chan = service::create_client::<Client>("simple service".into()).await.unwrap();
//!             cli(chan).await;
//!         },
//!         SchedulerType::RoundRobin,
//!     ).await;
//! }
//! ```
//!
//! ## Loop
//!
//! ```text
//!     Client                 Server
//! start: |                     | :start
//!        | --------------> u64 |
//!        | bool <------------- |
//!        |                     |
//!    goto start            goto start
//! ```
//!
//! ```
//! use t4os_async_lib::{service, session_types::*, scheduler::SchedulerType};
//!
//! // Define protocol.
//! type Server = Rec<Recv<u64, Send<bool, Var<Z>>>>;
//! type Client = <Server as HasDual>::Dual;
//!
//! async fn srv(chan: Chan<(), Server>) {
//!     let mut chan = chan.enter();
//!     loop {
//!         let (c, n) = chan.recv().await;
//!
//!         if n % 2 == 0 {
//!             chan = c.send(true).await.zero();
//!         } else {
//!             chan = c.send(false).await.zero();
//!         }
//!     }
//! }
//!
//! async fn cli(chan: Chan<(), Client>) {
//!     let mut chan = chan.enter();
//!     loop {
//!         let c = chan.send(9).await;
//!         let (c, _result) = c.recv().await;
//!         chan = c.zero();
//!     }
//! }
//! ```

use crate::{
    anydict::{AnyDict, AnyDictResult},
    channel::{unbounded, Receiver, RecvErr, Sender},
    session_types::{mk_chan, Chan, HasDual},
};
use alloc::borrow::Cow;
use core::{marker::PhantomData, sync::atomic::AtomicPtr};
use synctools::mcs::{MCSLock, MCSNode};

static SERVICES: MCSLock<Services> = MCSLock::new(Services::new());

type TxRx = (Sender<AtomicPtr<u8>>, Receiver<AtomicPtr<u8>>);

struct Services {
    services: AnyDict,
}

impl Services {
    const fn new() -> Self {
        Self {
            services: AnyDict::new(),
        }
    }

    /// `P` is a protocol of a server.
    fn create_server<P: 'static>(
        &mut self,
        name: Cow<'static, str>,
    ) -> Result<Accepter<P>, &'static str> {
        match self.services.get_mut::<InnerService<P>>(&name) {
            AnyDictResult::None => {
                let (inner, accepter) = InnerService::new_and_accepter();
                self.services.insert(name, inner);
                Ok(accepter)
            }
            AnyDictResult::Ok(s) => s
                .accepter
                .take()
                .ok_or("create_server: a server has been already created"),
            AnyDictResult::TypeError => Err("create_server: typing error"),
        }
    }

    /// `P` is a protocol of a client.
    fn create_client<P: HasDual + 'static>(
        &mut self,
        name: Cow<'static, str>,
    ) -> Result<Sender<TxRx>, &'static str> {
        match self.services.get_mut::<InnerService<P::Dual>>(&name) {
            AnyDictResult::None => {
                let inner = InnerService::<P::Dual>::new();
                let tx = inner.get_sender();
                self.services.insert(name, inner);
                tx
            }
            AnyDictResult::Ok(s) => s.get_sender(),
            AnyDictResult::TypeError => Err("create_client: typing error"),
        }
    }
}

/// `P` is a protocol of a server and `P::Dual` is a protocol of a client.
struct InnerService<P> {
    accepter: Option<Accepter<P>>,
    sender: Sender<TxRx>,
}

impl<P> InnerService<P> {
    fn new_and_accepter() -> (Self, Accepter<P>) {
        let (tx, rx) = unbounded();
        let accepter = Accepter::new(rx);

        (
            Self {
                accepter: None,
                sender: tx,
            },
            accepter,
        )
    }

    fn new() -> Self {
        let (tx, rx) = unbounded();
        Self {
            accepter: Some(Accepter::new(rx)),
            sender: tx,
        }
    }

    fn get_sender(&self) -> Result<Sender<TxRx>, &'static str> {
        if self.sender.is_terminated() {
            Err("channel has been terminated")
        } else {
            Ok(self.sender.clone())
        }
    }
}

/// `P` is a protocol of a server.
pub struct Accepter<P> {
    receiver: Receiver<TxRx>,
    _phantom: PhantomData<fn(P)>,
}

impl<P> Accepter<P> {
    fn new(receiver: Receiver<TxRx>) -> Self {
        Self {
            receiver,
            _phantom: Default::default(),
        }
    }

    pub async fn accept(&self) -> Result<Chan<(), P>, RecvErr> {
        let (tx, rx) = self.receiver.recv().await?;
        Ok(mk_chan(tx, rx))
    }
}

/// `P` is a protocol of a server.
pub fn create_server<P: 'static>(name: Cow<'static, str>) -> Result<Accepter<P>, &'static str> {
    let mut node = MCSNode::new();
    let mut services = SERVICES.lock(&mut node);
    services.create_server(name)
}

/// `P` is a protocol of a client.
pub async fn create_client<P: HasDual + 'static>(
    name: Cow<'static, str>,
) -> Result<Chan<(), P>, &'static str> {
    let mut node = MCSNode::new();
    let mut services = SERVICES.lock(&mut node);
    let tx = services.create_client::<P>(name)?;

    let (tx1, rx1) = unbounded();
    let (tx2, rx2) = unbounded();

    let client = mk_chan::<P>(tx1, rx2);
    tx.send((tx2, rx1)).await?;

    Ok(client)
}
