//! ROS2 like action, but this is connection oriented like TCP/IP.
//! Thus, an action server have to accept a connection from a client before starting an action.
//!
//! # Specification
//!
//! See [specification of action](https://github.com/tier4/t4os/tree/main/specification/awkernel_async_lib/src/action.rs).
//!
//! # Examples
//!
//! ## Action Server
//!
//! ```
//! use awkernel_async_lib::{
//!     action::{create_server, GoalResponse, ResultStatus, ServerFeedbackOrCancel, ServerRecvGoal},
//!     scheduler::SchedulerType,
//!     spawn,
//! };
//!
//! async fn server_task() {
//!     let server = create_server::<u64, u64, u64>("action_server".into()).unwrap();
//!
//!     // Accept a connection.
//!     while let Ok(server_recv_goal) = server.accept().await {
//!         spawn(server_main(server_recv_goal), SchedulerType::RoundRobin).await;
//!     }
//! }
//!
//! async fn server_main(mut server_recv_goal: ServerRecvGoal<u64, u64, u64>) {
//!     'outer: loop {
//!         // Receive a goal value.
//!         let Some((send_goal_result, goal)) = server_recv_goal.recv_goal().await
//!      else { /* The session have been closed. */ return };
//!
//!         // Send a goal result.
//!         let mut server_send_feedback = send_goal_result
//!             .accept(GoalResponse::AcceptAndExecute)
//!             .await;
//!
//!         // Send feedback values.
//!         let mut result = 0;
//!         for i in 0..=goal {
//!             result += i;
//!
//!             match server_send_feedback.send_feedback(result).await {
//!                 ServerFeedbackOrCancel::Feedback(f) => server_send_feedback = f,
//!                 ServerFeedbackOrCancel::Cancel(c) => {
//!                     server_recv_goal = c.send_cancel().await;
//!                     continue 'outer;
//!                 }
//!             }
//!         }
//!
//!         // Send a result value.
//!         server_recv_goal = server_send_feedback.send_result(result).await;
//!     }
//! }
//! ```
//!
//! ## Action Client
//!
//! ```
//! use awkernel_async_lib::{
//!     action::{create_client, AcceptOrRejectGoal, FeedbackOrResult},
//!     channel::bounded,
//! };
//!
//! async fn client() {
//!     let client_send_goal = create_client::<u64, u64, u64>("action_server".into())
//!         .await
//!         .unwrap();
//!
//!     let mut client_recv_feedback = match client_send_goal
//!         .send_goal(10, bounded::Attribute::default())
//!         .await
//!     {
//!         AcceptOrRejectGoal::Accept(client_recv_feedback, _id, _goal_response) => {
//!             client_recv_feedback
//!         }
//!         AcceptOrRejectGoal::Reject(client_send_goal) => {
//!             client_send_goal.close().await;
//!             return;
//!         }
//!     };
//!
//!     loop {
//!         match client_recv_feedback.recv().await {
//!             FeedbackOrResult::Feedback(rf, _feedback) => {
//!                 client_recv_feedback = rf;
//!             }
//!             FeedbackOrResult::Result(client_send_goal, result_status) => {
//!                 client_send_goal.close().await;
//!                 break;
//!             }
//!         }
//!     }
//! }
//! ```

use crate::{
    accepter::{Accepter, Services},
    channel::{bounded, unbounded},
    offer,
    session_types::{self as S},
};
use alloc::{
    borrow::Cow,
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    sync::Arc,
};
use core::{
    marker::PhantomData,
    result,
    sync::atomic::{AtomicBool, Ordering},
};
use futures::{
    future::{BoxFuture, Fuse},
    FutureExt,
};
use synctools::mcs::{MCSLock, MCSNode};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum GoalResponse {
    AcceptAndExecute,
    AcceptAndDefer,
}

#[derive(Debug, Clone)]
pub enum ResultStatus<R> {
    Succeeded(R),
    Canceled,
    Aborted,
}

static SERVICES: MCSLock<Services> = MCSLock::new(Services::new());
static ACTIONS: MCSLock<Actions> = MCSLock::new(Actions::new());

fn drop_accepter<P>(acc: &mut Accepter<P>) {
    let mut node = MCSNode::new();
    let mut guard = SERVICES.lock(&mut node);
    guard.set_accepter::<P>(acc.take());
}

type ProtoServer<G, F, R> = S::Rec<ProtoServerInn<G, F, R>>;
type ProtoClient<G, F, R> = <ProtoServer<G, F, R> as S::HasDual>::Dual;

type ProtoServerInn<G, F, R> = S::Offer<S::Eps /* Close. */, ProtoServerGoal<G, F, R>>;
type ProtoClientInn<G, F, R> = <ProtoServerInn<G, F, R> as S::HasDual>::Dual;

type ProtoServerGoal<G, F, R> = S::Recv<G /* Receive a goal. */, ProtoServerGoalResult<F, R>>;

type ProtoServerGoalResult<F, R> =
    S::Choose<S::Var<S::Z> /* Reject. */, ProtoServerSendGoalResult<F, R> /* Accept. */>;

type ProtoServerSendGoalResult<F, R> = S::Send<
    (u64, GoalResponse), /* Send an ID and a response of the goal. */
    ProtoServerFeedback<F, R>,
>;

type ProtoServerFeedback<F, R> = S::Recv<
    bounded::Attribute, /* Receive an attribute. */
    S::Send<bounded::Receiver<F> /* Send Rx. */, ProtoServerResult<R>>,
>;

type ProtoServerResult<R> = S::Send<
    ResultStatus<R>, /* Send a result. */
    S::Var<S::Z>,    /* Goto ProtoServerInn. */
>;

#[must_use]
pub struct ServerRecvGoal<G, F, R> {
    chan: S::Chan<(ProtoServerInn<G, F, R>, ()), ProtoServerInn<G, F, R>>,
    name: Cow<'static, str>,
}

impl<G, F, R> ServerRecvGoal<G, F, R>
where
    G: Send + 'static,
{
    /// Receive a goal.
    /// If a goal is received, a value of `Some((ServerSendGoalResult, G))` will be returned.
    /// If the session is closed by remote, `None` will be returned.
    pub async fn recv_goal(self) -> Option<(ServerSendGoalResult<G, F, R>, G)> {
        let c = self.chan;
        offer! {c,
            CLOSE => {
                c.close();
                None
            },
            RECV => {
                let (chan, goal) = c.recv().await;
                Some((ServerSendGoalResult{ chan, name: self.name }, goal))
            }
        }
    }
}

#[must_use]
pub struct ServerSendGoalResult<G, F, R> {
    chan: S::Chan<(ProtoServerInn<G, F, R>, ()), ProtoServerGoalResult<F, R>>,
    name: Cow<'static, str>,
}

impl<G, F, R> ServerSendGoalResult<G, F, R>
where
    F: Send + 'static,
{
    /// Reject a goal value received before.
    /// The state will be transited from `ServerSendGoalResult` to `ServerRecvGoal`.
    pub async fn reject(self) -> ServerRecvGoal<G, F, R> {
        let c = self.chan;
        let c = c.sel1().await;
        let chan = c.zero();
        ServerRecvGoal {
            chan,
            name: self.name,
        }
    }

    /// Accept a goal value received before.
    /// The state will be transited from `ServerSendGoalResult` to `ServerSendFeedback`.
    pub async fn accept(self, response: GoalResponse) -> ServerSendFeedback<G, F, R> {
        let cancel = Arc::new(AtomicBool::new(false));
        let id = {
            let mut node = MCSNode::new();
            let mut actions = ACTIONS.lock(&mut node);
            actions.insert(self.name.clone(), cancel.clone())
        };

        let c = self.chan;
        let c = c.sel2().await;
        let c = c.send((id, response)).await;
        let (c, attribute) = c.recv().await;

        let (tx, rx) = bounded::new(attribute);
        let chan = c.send(rx).await;

        ServerSendFeedback {
            chan,
            name: self.name,
            tx,
            cancel,
            id,
        }
    }
}

pub enum ServerFeedbackOrCancel<G, F, R> {
    Feedback(ServerSendFeedback<G, F, R>),
    Cancel(ServerSendCancel<G, F, R>),
}

#[must_use]
pub struct ServerSendFeedback<G, F, R> {
    chan: S::Chan<(ProtoServerInn<G, F, R>, ()), ProtoServerResult<R>>,
    name: Cow<'static, str>,
    tx: bounded::Sender<F>,
    cancel: Arc<AtomicBool>,
    id: u64,
}

impl<G, F, R> ServerSendFeedback<G, F, R>
where
    F: Send + 'static,
    R: Send + 'static,
{
    /// Send a feedback value.
    /// The state will be transited from `ServerSendFeedback` to `ServerSendFeedback` or `ServerSendCancel`.
    pub async fn send_feedback(self, feedback: F) -> ServerFeedbackOrCancel<G, F, R> {
        if self.cancel.load(Ordering::Relaxed) {
            ServerFeedbackOrCancel::Cancel(ServerSendCancel {
                chan: self.chan,
                name: self.name,
                cancel: self.cancel,
            })
        } else {
            self.tx.send(feedback).await.unwrap();
            ServerFeedbackOrCancel::Feedback(self)
        }
    }

    /// Send a result value.
    /// The state will be transited from `ServerSendFeedback` to `ServerRecvGoal`.
    pub async fn send_result(self, result: R) -> ServerRecvGoal<G, F, R> {
        remove_cancel(&self.name, self.id);

        let c = self.chan;
        let c = c.send(ResultStatus::Succeeded(result)).await;
        let chan = c.zero();

        ServerRecvGoal {
            chan,
            name: self.name,
        }
    }

    /// Send abort.
    /// The state will be transited from `ServerSendFeedback` to `ServerRecvGoal`.
    pub async fn send_abort(self) -> ServerRecvGoal<G, F, R> {
        remove_cancel(&self.name, self.id);

        let c = self.chan;
        let c = c.send(ResultStatus::Aborted).await;
        let chan = c.zero();
        ServerRecvGoal {
            chan,
            name: self.name,
        }
    }
}

#[must_use]
pub struct ServerSendCancel<G, F, R> {
    chan: S::Chan<(ProtoServerInn<G, F, R>, ()), ProtoServerResult<R>>,
    name: Cow<'static, str>,
    cancel: Arc<AtomicBool>,
}

impl<G, F, R> ServerSendCancel<G, F, R>
where
    F: Send + 'static,
    R: Send + 'static,
{
    /// Send a cancel.
    /// The state will be transited from `ServerSendCancel` to `ServerRecvGoal`.
    pub async fn send_cancel(self) -> ServerRecvGoal<G, F, R> {
        let c = self.chan;
        let c = c.send(ResultStatus::Canceled).await;
        let chan = c.zero();

        self.cancel.store(false, Ordering::Relaxed);

        ServerRecvGoal {
            chan,
            name: self.name,
        }
    }
}

type ChanClient<G, F, R> = S::Chan<(ProtoClientInn<G, F, R>, ()), ProtoClientInn<G, F, R>>;

#[must_use]
pub struct ClientSendGoal<'a, G, F, R> {
    chan: ChanClient<G, F, R>,
    _phantom: PhantomData<&'a ()>,
}

#[must_use]
pub enum AcceptOrRejectGoal<'a, G, F, R> {
    Accept(ClientRecvFeedback<'a, G, F, R>, u64, GoalResponse),
    Reject(ClientSendGoal<'a, G, F, R>),
}

impl<'a, G, F, R> ClientSendGoal<'a, G, F, R>
where
    G: Send + 'static,
    F: Send + 'static,
    R: Send + 'static,
{
    /// Send a goal value.
    /// The state will be transited from `ClientSendGoal` to `ClientRecvFeedback` if the goal value sent before has been accepted.
    ///
    /// `attribute` is a channel attribute for feedback values.
    pub async fn send_goal(
        self,
        goal: G,
        attribute: bounded::Attribute,
    ) -> AcceptOrRejectGoal<'a, G, F, R> {
        let c = self.chan;
        let c = c.sel2().await;
        let c = c.send(goal).await;

        offer! {c,
            REJECT => {
                let chan = c.zero();
                AcceptOrRejectGoal::Reject(Self { chan, _phantom: PhantomData::default() })
            },
            ACCEPT => {
                let (c, (id, response)) = c.recv().await;
                let c = c.send(attribute).await;
                let (c, rx) = c.recv().await;

                let chan = async move {
                    c.recv().await
                }.boxed().fuse();

                let rx = async move {
                    rx.recv().await
                }.boxed().fuse();

                AcceptOrRejectGoal::Accept(ClientRecvFeedback { chan, rx }, id, response)
            }
        }
    }

    /// Close this session.
    pub async fn close(self) {
        self.chan.sel1().await.close();
    }
}

type ChanClientChoose<G, F, R> = S::Chan<(ProtoClientInn<G, F, R>, ()), S::Var<S::Z>>;

#[must_use]
pub struct ClientRecvFeedback<'a, G, F, R> {
    chan: Fuse<BoxFuture<'a, (ChanClientChoose<G, F, R>, ResultStatus<R>)>>,
    rx: Fuse<BoxFuture<'a, Result<F, bounded::RecvErr>>>,
}

#[must_use]
pub enum FeedbackOrResult<'a, G, F, R> {
    Feedback(ClientRecvFeedback<'a, G, F, R>, F),
    Result(ClientSendGoal<'a, G, F, R>, ResultStatus<R>),
}

impl<'a, G, F, R> ClientRecvFeedback<'a, G, F, R>
where
    G: Send + 'static,
    F: Send + 'static,
    R: Send + 'static,
{
    /// Receive a feedback or result value.
    pub async fn recv(self) -> FeedbackOrResult<'a, G, F, R> {
        let (mut chan, mut rx) = (self.chan, self.rx);

        futures::select_biased! {
            (c, status) = chan => {
                FeedbackOrResult::Result(ClientSendGoal { chan: c.zero(), _phantom: PhantomData::default() } , status)
            },
            result = rx => {
                let feedback = result.unwrap();
                FeedbackOrResult::Feedback(ClientRecvFeedback{ chan, rx }, feedback)
            }
        }
    }
}

/// Create a server.
///
/// - `G`: type of goal.
/// - `F`: type of feedback.
/// - `R`: type of result.
pub fn create_server<G, F, R>(
    name: Cow<'static, str>,
) -> Result<ActionAccepter<G, F, R>, &'static str> {
    let mut node = MCSNode::new();
    let mut services = SERVICES.lock(&mut node);
    let accepter = services.create_server(name.clone(), drop_accepter)?;
    Ok(ActionAccepter { accepter, name })
}

/// Create a client.
///
/// - `G`: type of goal.
/// - `F`: type of feedback.
/// - `R`: type of result.
pub async fn create_client<G: 'static, F: 'static, R: 'static>(
    name: Cow<'static, str>,
) -> Result<ClientSendGoal<G, F, R>, &'static str> {
    let mut node = MCSNode::new();
    let mut services = SERVICES.lock(&mut node);
    let tx = services.create_client::<ProtoClient<G, F, R>>(name, drop_accepter)?;

    let (tx1, rx1) = unbounded::new();
    let (tx2, rx2) = unbounded::new();

    let chan = S::mk_chan::<ProtoClient<G, F, R>>(tx1, rx2);
    tx.send((tx2, rx1)).await?;

    let chan = chan.enter();

    Ok(ClientSendGoal {
        chan,
        _phantom: PhantomData::default(),
    })
}

pub struct ActionAccepter<G: 'static, F: 'static, R: 'static> {
    accepter: Accepter<ProtoServer<G, F, R>>,
    name: Cow<'static, str>,
}

impl<G: 'static, F: 'static, R: 'static> ActionAccepter<G, F, R> {
    /// Accept a connection.
    pub async fn accept(&self) -> Result<ServerRecvGoal<G, F, R>, unbounded::RecvErr> {
        let chan = self.accepter.accept().await?;
        let chan = chan.enter();
        Ok(ServerRecvGoal {
            chan,
            name: self.name.clone(),
        })
    }
}

type ActionMap = BTreeMap<Cow<'static, str>, BTreeMap<u64, Arc<AtomicBool>>>;

struct Actions {
    ids: BTreeMap<Cow<'static, str>, BTreeMap<u64, Arc<AtomicBool>>>,
    current_id: u64,
}

impl Actions {
    const fn new() -> Self {
        Actions {
            ids: BTreeMap::new(),
            current_id: 0,
        }
    }

    fn get_actions(&self) -> BTreeMap<Cow<'static, str>, BTreeSet<u64>> {
        let mut result = BTreeMap::new();
        for (name, map) in self.ids.iter() {
            let mut set = BTreeSet::new();
            for id in map.keys() {
                set.insert(*id);
            }

            result.insert(name.clone(), set);
        }

        result
    }

    fn insert(&mut self, name: Cow<'static, str>, flag: Arc<AtomicBool>) -> u64 {
        fn get_id(map: &BTreeMap<u64, Arc<AtomicBool>>, start: &mut u64) -> u64 {
            loop {
                let result = *start;
                *start += 1;
                if !map.contains_key(&result) {
                    return result;
                }
            }
        }

        match self.ids.entry(name.into()) {
            Entry::Occupied(mut e) => {
                let map = e.get_mut();
                let id = get_id(map, &mut self.current_id);
                map.insert(id, flag);
                id
            }
            Entry::Vacant(e) => {
                let mut map = BTreeMap::new();
                let id = get_id(&mut map, &mut self.current_id);
                map.insert(id, flag);
                e.insert(map);
                id
            }
        }
    }

    fn remove(&mut self, name: &str, id: u64) {
        if let Some(map) = self.ids.get_mut(name) {
            map.remove(&id);
            if map.is_empty() {
                self.ids.remove(name);
            }
        }
    }

    fn cancel(&mut self, name: &str, id: u64) {
        if let Some(map) = self.ids.get_mut(name) {
            if let Some(flag) = map.get(&id) {
                flag.store(true, Ordering::Relaxed);

                map.remove(&id);
                if map.is_empty() {
                    self.ids.remove(name);
                }
            }
        }
    }

    fn cancel_all(&mut self, name: &str) {
        if let Some(map) = self.ids.get_mut(name) {
            for flag in map.values() {
                flag.store(true, Ordering::Relaxed);
            }

            self.ids.remove(name);
        }
    }
}

pub fn cancel(name: &str, id: u64) {
    let mut node = MCSNode::new();
    let mut actions = ACTIONS.lock(&mut node);
    actions.cancel(name, id);
}

pub fn cancel_all(name: &str) {
    let mut node = MCSNode::new();
    let mut actions = ACTIONS.lock(&mut node);
    actions.cancel_all(name);
}

fn remove_cancel(name: &str, id: u64) {
    let mut node = MCSNode::new();
    let mut actions = ACTIONS.lock(&mut node);
    actions.remove(name, id);
}

pub fn get_actions() -> BTreeMap<Cow<'static, str>, BTreeSet<u64>> {
    let mut node = MCSNode::new();
    let actions = ACTIONS.lock(&mut node);
    actions.get_actions()
}
