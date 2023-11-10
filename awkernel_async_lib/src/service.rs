//! Client and server model communication.
//!
//! # Examples
//!
//! ## A Simple Protocol
//!
//! The protocol is as follows.
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
//! use awkernel_async_lib::{service, session_types::*, scheduler::SchedulerType};
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
//!     let server = service::create_server::<Server>("simple service".into()).unwrap();
//!
//!     // Spawn a server.
//!     awkernel_async_lib::spawn(
//!         "server".into(),
//!         async move {
//!             while let Ok(chan) = server.accept().await {
//!                 // Spawn a task for the connection.
//!                 awkernel_async_lib::spawn(
//!                     "connection".into(),
//!                     async move {
//!                         srv(chan).await;
//!                     },
//!                     SchedulerType::FIFO,
//!                 ).await;
//!             }
//!         },
//!         SchedulerType::FIFO,
//!     ).await;
//!
//!     // Start a client.
//!     awkernel_async_lib::spawn(
//!         "client".into(),
//!         async {
//!             let chan = service::create_client::<Client>("simple service".into()).await.unwrap();
//!             cli(chan).await;
//!         },
//!         SchedulerType::FIFO,
//!     ).await;
//! }
//! ```
//!
//! ## Loop
//!
//! The protocol is as follows.
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
//! use awkernel_async_lib::session_types::*;
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
//!
//! ## Offer and Choose
//!
//! The protocol is as follows.
//!
//! ```text
//! Client                 Server
//!    |                     |
//!    | --------------> u64 |
//!    |       or            |
//!    | -----------> String |
//!    |                     |
//!  close                 close
//! ```
//!
//! ```
//! use awkernel_async_lib::{offer, session_types::*};
//!
//! type Server = Offer<Recv<u64, Eps>, Recv<String, Eps>>;
//! type Client = <Server as HasDual>::Dual;
//!
//! async fn srv(c: Chan<(), Server>) {
//!     offer! {c,
//!         Number => { // 1st protocol.
//!             let (c, _result) = c.recv().await;
//!             c.close();
//!         },
//!         String => { // 2nd protocol.
//!             let (c, _result) = c.recv().await;
//!             c.close();
//!         }
//!     }
//! }
//!
//! async fn cli(c: Chan<(), Client>) {
//!     let c = c.sel2().await; // Choose 2nd protocol (String).
//!     let c = c.send("Hello, world!".to_string()).await;
//!     c.close();
//! }
//! ```
//!
//! ## Proxy
//!
//! 1. A client create endpoints for the client and a server.
//! 2. The client sends the endpoint of the server to a proxy.
//! 3. The proxy receives the endpoint from the client and forwards it to the server.
//! 4. The server receives the endpoint.
//! 5. The client sends a `u64` value to the endpoint created at Step 1.
//! 6. The server receives the `u64` value from the received endpoint.
//!
//! ```text
//!   Client                       Proxy                        Server
//!   |   |                         |  |                         |   |
//!   |   | ---> endpoint to server |  |                         |   |
//!   |   |                         |  | ---> endpoint to server |   |
//!   | close                   close  close                   close |
//!   |                                                              |
//!   | -------------------------------------------------------> u64 |
//!   |                                                              |
//! close                                                          close
//! ```
//!
//! ```
//! use awkernel_async_lib::{service, session_types::*, scheduler::SchedulerType};
//!
//! // Define protocol.
//! type Server = Recv<u64, Eps>;
//! type ProxySrv1 = Recv<SrvChan, Eps>;
//! type ProxyCli1 = <ProxySrv1 as HasDual>::Dual;
//! type ProxySrv2 = Send<SrvChan, Eps>;
//! type ProxyCli2 = <ProxySrv2 as HasDual>::Dual;
//!
//! type SrvChan = Chan<(), Server>; // Channel type of server.
//!
//! /// Client.
//! async fn cli(c: Chan<(), ProxyCli1>) {
//!     let (server, client) = session_channel::<Server>();
//!     let pr = c.send(server).await; // Send the endpoint to a server.
//!     pr.close();
//!
//!     let c = client.send(123).await; // Send a `u64` value.
//!     c.close();
//! }
//!
//! /// Server.
//! async fn srv(c: Chan<(), ProxyCli2>) {
//!     let (pr, server) = c.recv().await; // Receive an endpoint.
//!     pr.close();
//!
//!     let (c, _result) = server.recv().await; // Receive a value from the endpoint.
//!     c.close();
//! }
//!
//! async fn proxy(c1: Chan<(), ProxySrv1>, c2: Chan<(), ProxySrv2>) {
//!     let (c1, server) = c1.recv().await; // Receive an endpoint.
//!     c1.close();
//!
//!     let c2 = c2.send(server).await; // Forward the endpoint.
//!     c2.close();
//! }
//!
//! let _ = async {
//!     let (pr_srv1, pr_cli1) = session_channel::<ProxySrv1>(); // Channel between client and proxy.
//!     let (pr_srv2, pr_cli2) = session_channel::<ProxySrv2>(); // Channel between proxy and server.
//!
//!     awkernel_async_lib::spawn("cli1".into(), async move { cli(pr_cli1).await; }, SchedulerType::FIFO,).await;
//!     awkernel_async_lib::spawn("cli2".into(), async move { srv(pr_cli2).await; }, SchedulerType::FIFO,).await;
//!     awkernel_async_lib::spawn("proxy".into(), async move { proxy(pr_srv1, pr_srv2).await; }, SchedulerType::FIFO).await;
//! };
//! ```

use crate::{
    accepter::{self, Accepter, Services},
    channel::unbounded,
    session_types::{mk_chan, Chan, HasDual},
};
use alloc::{borrow::Cow, vec::Vec};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

static SERVICES: Mutex<Services> = Mutex::new(Services::new());

fn drop_accepter<P>(acc: &mut Accepter<P>) {
    let mut node = MCSNode::new();
    let mut guard = SERVICES.lock(&mut node);
    guard.set_accepter::<P>(acc.take());
}

/// Create a server.
/// `P` is a protocol of a server defined by session types.
///
/// # Example
///
/// ```
/// use awkernel_async_lib::{service, session_types::*, scheduler::SchedulerType};
///
/// type Server = Recv<u64, Send<bool, Eps>>;
///
/// let server = service::create_server::<Server>("service name".into()).unwrap();
///
/// let _ = async move {
///     while let Ok(chan) = server.accept().await {
///        // Spawn a task for the connection.
///         awkernel_async_lib::spawn(
///             "server".into(),
///             async move {
///                 let (c, n) = chan.recv().await;
///                 let c = c.send(n % 2 == 1).await;
///                 c.close();
///             },
///             SchedulerType::FIFO,
///         ).await;
///     }
/// };
/// ```
pub fn create_server<P: 'static>(name: Cow<'static, str>) -> Result<Accepter<P>, &'static str> {
    let mut node = MCSNode::new();
    let mut services = SERVICES.lock(&mut node);
    services.create_server(name, drop_accepter)
}

/// Create a client.
/// `P` is a protocol of a client.
///
/// # Example
///
/// ```
/// use awkernel_async_lib::{service, session_types::*, scheduler::SchedulerType};
///
/// type Client = Send<u64, Recv<bool, Eps>>;
///
/// let _ = async {
///     let client = service::create_client::<Client>("service name".into()).await.unwrap();
///
///     let c = client.send(9).await;
///     let (c, result) = c.recv().await;
///     c.close();
/// };
/// ```
pub async fn create_client<P: HasDual + 'static>(
    name: Cow<'static, str>,
) -> Result<Chan<(), P>, &'static str> {
    let tx = get_tx::<P>(name)?;

    let (tx1, rx1) = unbounded::new();
    let (tx2, rx2) = unbounded::new();

    let client = mk_chan::<P>(tx1, rx2);
    tx.send((tx2, rx1)).await?;

    Ok(client)
}

fn get_tx<P: HasDual + 'static>(
    name: Cow<'static, str>,
) -> Result<unbounded::Sender<accepter::TxRx>, &'static str> {
    let mut node = MCSNode::new();
    let mut services = SERVICES.lock(&mut node);
    services.create_client::<P>(name, drop_accepter)
}

pub fn get_services() -> Vec<Cow<'static, str>> {
    let mut node = MCSNode::new();
    let services = SERVICES.lock(&mut node);
    services.get_services()
}
