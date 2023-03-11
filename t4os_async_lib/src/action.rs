//! ROS2 like action.
//!
//! # Specification
//!
//! See [specification of action](https://github.com/tier4/t4os/tree/main/specification/t4os_async_lib/src/action.rs).

use crate::{
    channel::bounded,
    offer,
    session_types::{self as S},
};
use core::marker::PhantomData;
use futures::{
    future::{BoxFuture, Fuse},
    FutureExt,
};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum GoalResponse {
    AcceptAndExecute,
    AcceptAndDefer,
}

#[derive(Debug, Clone)]
pub enum ResultStatus {
    Succeeded,
    Canceled,
    Aborted,
}

type ProtoServer<G, F, R> = S::Rec<ProtoServerInn<G, F, R>>;

type ProtoServerInn<G, F, R> = S::Offer<S::Eps /* Close. */, ProtoServerGoal<G, F, R>>;
type ProtoClientInn<G, F, R> = <ProtoServerInn<G, F, R> as S::HasDual>::Dual;

type ProtoServerGoal<G, F, R> = S::Recv<G /* Receive a goal. */, ProtoServerGoalResult<F, R>>;

type ProtoServerGoalResult<F, R> =
    S::Choose<S::Var<S::Z> /* Reject. */, ProtoServerSendGoalResult<F, R> /* Accept. */>;

type ProtoServerSendGoalResult<F, R> =
    S::Send<GoalResponse /* Send a response of the goal. */, ProtoServerFeedback<F, R>>;

type ProtoServerFeedback<F, R> = S::Recv<
    bounded::Attribute, /* Receive an attribute. */
    S::Send<bounded::Receiver<F> /* Send Rx. */, ProtoServerResult<R>>,
>;

type ProtoServerResult<R> = S::Send<
    (ResultStatus, R), /* Send a result. */
    S::Var<S::Z>,      /* Goto ProtoServerInn. */
>;

#[must_use]
pub struct ServerRecvGoal<G, F, R> {
    chan: S::Chan<(ProtoServerInn<G, F, R>, ()), ProtoServerInn<G, F, R>>,
}

impl<G, F, R> ServerRecvGoal<G, F, R>
where
    G: Send + 'static,
{
    pub async fn recv_goal(self) -> Option<(ServerSendGoalResult<G, F, R>, G)> {
        let c = self.chan;
        offer! {c,
            CLOSE => {
                c.close();
                None
            },
            RECV => {
                let (chan, goal) = c.recv().await;
                Some((ServerSendGoalResult{ chan },goal))
            }
        }
    }
}

#[must_use]
pub struct ServerSendGoalResult<G, F, R> {
    chan: S::Chan<(ProtoServerInn<G, F, R>, ()), ProtoServerGoalResult<F, R>>,
}

impl<G, F, R> ServerSendGoalResult<G, F, R>
where
    F: Send + 'static,
{
    pub async fn reject(self) -> ServerRecvGoal<G, F, R> {
        let c = self.chan;
        let c = c.sel1().await;
        let chan = c.zero();
        ServerRecvGoal { chan }
    }

    pub async fn accept_and_execute(self) -> ServerSendFeedback<G, F, R> {
        self.accept(GoalResponse::AcceptAndExecute).await
    }

    pub async fn accept_and_defer(self) -> ServerSendFeedback<G, F, R> {
        self.accept(GoalResponse::AcceptAndDefer).await
    }

    pub async fn accept(self, response: GoalResponse) -> ServerSendFeedback<G, F, R> {
        let c = self.chan;
        let c = c.sel2().await;
        let c = c.send(response).await;
        let (c, attribute) = c.recv().await;

        let (tx, rx) = bounded::new(attribute);
        let chan = c.send(rx).await;

        ServerSendFeedback { chan, tx }
    }
}

#[must_use]
pub struct ServerSendFeedback<G, F, R> {
    chan: S::Chan<(ProtoServerInn<G, F, R>, ()), ProtoServerResult<R>>,
    tx: bounded::Sender<F>,
}

impl<G, F, R> ServerSendFeedback<G, F, R>
where
    F: Send + 'static,
    R: Send + 'static,
{
    pub async fn send_feedback(&self, feedback: F) -> Result<(), bounded::SendErr> {
        self.tx.send(feedback).await
    }

    pub async fn send_result(self, status: ResultStatus, value: R) -> ServerRecvGoal<G, F, R> {
        let c = self.chan;
        let c = c.send((status, value)).await;
        let chan = c.zero();
        ServerRecvGoal { chan }
    }
}

type ChanClient<G, F, R> = S::Chan<(ProtoClientInn<G, F, R>, ()), ProtoClientInn<G, F, R>>;

#[must_use]
pub struct ClientSendGoal<'a, G, F, R> {
    chan: ChanClient<G, F, R>,
    _phantom: PhantomData<&'a ()>,
}

pub enum AcceptOrRejectGoal<'a, G, F, R> {
    Accept(ClientRecvFeedback<'a, G, F, R>, GoalResponse),
    Reject(ClientSendGoal<'a, G, F, R>),
}

impl<'a, G, F, R> ClientSendGoal<'a, G, F, R>
where
    G: Send + 'static,
    F: Send + 'static,
    R: Send + 'static,
{
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
                let (c, response) = c.recv().await;
                let c = c.send(attribute).await;
                let (c, rx) = c.recv().await;

                let chan = async move {
                    c.recv().await
                }.boxed().fuse();

                let rx = async move {
                    rx.recv().await
                }.boxed().fuse();

                AcceptOrRejectGoal::Accept(ClientRecvFeedback { chan, rx }, response)
            }
        }
    }

    pub async fn close(self) {
        self.chan.sel1().await.close();
    }
}

type ChanClientChoose<G, F, R> = S::Chan<(ProtoClientInn<G, F, R>, ()), S::Var<S::Z>>;

#[must_use]
pub struct ClientRecvFeedback<'a, G, F, R> {
    chan: Fuse<BoxFuture<'a, (ChanClientChoose<G, F, R>, (ResultStatus, R))>>,
    rx: Fuse<BoxFuture<'a, Result<F, bounded::RecvErr>>>,
}

#[must_use]
pub enum FeedbackOrResult<'a, G, F, R> {
    Feedback(ClientRecvFeedback<'a, G, F, R>, F),
    Result(ClientSendGoal<'a, G, F, R>, ResultStatus, R),
}

impl<'a, G, F, R> ClientRecvFeedback<'a, G, F, R>
where
    G: Send + 'static,
    F: Send + 'static,
    R: Send + 'static,
{
    pub async fn recv(self) -> FeedbackOrResult<'a, G, F, R> {
        let (mut chan, mut rx) = (self.chan, self.rx);

        futures::select_biased! {
            (c, (status ,response)) = chan => {
                FeedbackOrResult::Result(ClientSendGoal { chan: c.zero(), _phantom: PhantomData::default() } , status, response)
            },
            result = rx => {
                let feedback = result.unwrap();
                FeedbackOrResult::Feedback(ClientRecvFeedback{ chan, rx }, feedback)
            }
        }
    }
}
