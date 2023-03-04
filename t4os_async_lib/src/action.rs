//! ROS2 like action.
//!
//! # Specification
//!
//! See [specification of action](https://github.com/tier4/t4os/tree/main/specification/t4os_async_lib/src/action.rs).

use crate::{offer, session_types as S};

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

type ProtoServerGoalResult<F, R> = S::Choose<
    S::Var<S::Z>, /* Reject. */
    S::Send<GoalResponse /* Send a response of the goal. */, ProtoServerFeedback<F, R>>,
>;

type ProtoServerFeedback<F, R> = S::Rec<ProtoServerFeedbackInn<F, R>>;

type ProtoServerFeedbackInn<F, R> = S::Choose<
    S::Send<F /* Send a feedback. */, S::Var<S::Z> /* Goto ProtoServerFeedbackInn. */>,
    S::Send<
        (ResultStatus, R),  /* Send a result. */
        S::Var<S::S<S::Z>>, /* Goto ProtoServerInn. */
    >,
>;
type ProtoClientFeedbackInn<F, R> = <ProtoServerFeedbackInn<F, R> as S::HasDual>::Dual;

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
        let chan = c.enter();

        ServerSendFeedback { chan }
    }
}

#[must_use]
pub struct ServerSendFeedback<G, F, R> {
    chan: S::Chan<
        (ProtoServerFeedbackInn<F, R>, (ProtoServerInn<G, F, R>, ())),
        ProtoServerFeedbackInn<F, R>,
    >,
}

impl<G, F, R> ServerSendFeedback<G, F, R>
where
    F: Send + 'static,
    R: Send + 'static,
{
    pub async fn send_feedback(self, feedback: F) -> Self {
        let c = self.chan;
        let c = c.sel1().await;
        let c = c.send(feedback).await;
        let chan = c.zero();
        Self { chan }
    }

    pub async fn send_result(self, status: ResultStatus, value: R) -> ServerRecvGoal<G, F, R> {
        let c = self.chan;
        let c = c.sel2().await;
        let c = c.send((status, value)).await;
        let chan = c.succ().zero();
        ServerRecvGoal { chan }
    }
}

#[must_use]
pub struct ClientSendGoal<G, F, R> {
    chan: S::Chan<(ProtoClientInn<G, F, R>, ()), ProtoClientInn<G, F, R>>,
}

pub enum AcceptOrRejectGoal<G, F, R> {
    Accept(ClientRecvFeedback<G, F, R>, GoalResponse),
    Reject(ClientSendGoal<G, F, R>),
}

impl<G, F, R> ClientSendGoal<G, F, R>
where
    G: Send + 'static,
{
    pub async fn send_goal(self, goal: G) -> AcceptOrRejectGoal<G, F, R> {
        let c = self.chan;
        let c = c.sel2().await;
        let c = c.send(goal).await;

        offer! {c,
            REJECT => {
                let chan = c.zero();
                AcceptOrRejectGoal::Reject(Self { chan })
            },
            ACCEPT => {
                let (c, response) = c.recv().await;
                let chan = c.enter();
                AcceptOrRejectGoal::Accept(ClientRecvFeedback { chan }, response)
            }
        }
    }
}

#[must_use]
pub struct ClientRecvFeedback<G, F, R> {
    chan: S::Chan<
        (ProtoClientFeedbackInn<F, R>, (ProtoClientInn<G, F, R>, ())),
        ProtoClientFeedbackInn<F, R>,
    >,
}

pub enum FeedbackOrResult<G, F, R> {
    Feedback(ClientRecvFeedback<G, F, R>, F),
    Result(ClientSendGoal<G, F, R>, ResultStatus, R),
}

impl<G, F, R> ClientRecvFeedback<G, F, R>
where
    F: Send + 'static,
    R: Send + 'static,
{
    pub async fn recv(self) -> FeedbackOrResult<G, F, R> {
        let c = self.chan;
        offer! {c,
            FEEDBACK => {
                let (c, value) = c.recv().await;
                let chan = c.zero();
                FeedbackOrResult::Feedback(Self{ chan }, value)
            },
            RESULT => {
                let (c, (status, response)) = c.recv().await;
                let chan = c.succ().zero();
                FeedbackOrResult::Result(ClientSendGoal { chan }, status, response)
            }
        }
    }
}
