use crate::{
    offer,
    pubsub::{Publisher, Subscriber},
    session_types,
};
use core::marker::PhantomData;
use session_types as S;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum GoalResponse {
    Reject,
    AcceptAndExecute,
    AcceptAndDefer,
}

#[derive(Debug, Clone)]
pub enum ResultStatus {
    Succeeded,
    Canceled,
    Aborted,
}

#[derive(Debug, Clone)]
pub enum GoalStatus {
    Accepted,
    Executing,
    Canceling,
    Succeeded,
    Canceled,
    Aborted,
}

#[derive(Clone)]
pub struct Feedback<T: Send> {
    pub status: GoalStatus,
    pub value: T,
}

#[derive(Clone)]
pub struct ActionResult<T> {
    pub status: ResultStatus,
    pub value: T,
}

type GoalSrvInner<T> = S::Offer<S::Eps, S::Recv<T, S::Send<GoalResponse, S::Var<S::Z>>>>;
type GoalCliInner<T> = <GoalSrvInner<T> as S::HasDual>::Dual;

type ResultSrvInner<T> = S::Offer<S::Eps, S::Recv<(), S::Send<ActionResult<T>, S::Var<S::Z>>>>;
type ResultCliInner<T> = <ResultSrvInner<T> as S::HasDual>::Dual;

pub struct ClientGoal; // Goal state.
pub struct ClientFeedback; // Feedback state.
pub struct ClientResult; // ResultState

#[must_use]
pub enum FeedbackOrResult<T1, T2> {
    Feedback(T1),
    Result(T2),
}

type GoalClient<GOAL, E1> = S::Chan<(GoalCliInner<GOAL>, E1), GoalCliInner<GOAL>>;
type ResultClient<RESULT, E2> = S::Chan<(ResultCliInner<RESULT>, E2), ResultCliInner<RESULT>>;

#[must_use]
pub struct ActionClient<STATE, GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Send + Clone + 'static,
{
    goal_client: GoalClient<GOAL, E1>,
    subscriber: Subscriber<Feedback<FEEDBACK>>,
    result_client: ResultClient<RESULT, E2>,
    _phantom: PhantomData<STATE>,
}

impl<STATE, GOAL, FEEDBACK, RESULT, E1, E2> ActionClient<STATE, GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Send + Clone + 'static,
{
    fn split(
        self,
    ) -> (
        GoalClient<GOAL, E1>,
        Subscriber<Feedback<FEEDBACK>>,
        ResultClient<RESULT, E2>,
    ) {
        (self.goal_client, self.subscriber, self.result_client)
    }
}

impl<GOAL, FEEDBACK, RESULT, E1, E2> ActionClient<ClientGoal, GOAL, FEEDBACK, RESULT, E1, E2>
where
    GOAL: Send + 'static,
    FEEDBACK: Send + Clone + 'static,
{
    pub async fn send_goal(
        self,
        goal: GOAL,
    ) -> Result<
        ActionClient<ClientFeedback, GOAL, FEEDBACK, RESULT, E1, E2>,
        ActionClient<ClientGoal, GOAL, FEEDBACK, RESULT, E1, E2>,
    > {
        let (goal_client, subscriber, result_client) = self.split();
        let goal_client = goal_client.sel2().await;
        let goal_client = goal_client.send(goal).await;
        let (goal_client, result) = goal_client.recv().await;
        let goal_client = goal_client.zero();

        if matches!(result, GoalResponse::Reject) {
            Ok(ActionClient {
                goal_client,
                subscriber,
                result_client,
                _phantom: PhantomData::default(),
            })
        } else {
            Err(ActionClient {
                goal_client,
                subscriber,
                result_client,
                _phantom: PhantomData::default(),
            })
        }
    }

    pub async fn close(self) {
        let (goal_client, _, result_client) = self.split();
        goal_client.sel1().await.close();
        result_client.sel1().await.close();
    }
}

impl<GOAL, FEEDBACK, RESULT, E1, E2> ActionClient<ClientFeedback, GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Send + Clone + 'static,
{
    pub async fn recv_feedback(
        self,
    ) -> FeedbackOrResult<
        (Self, Feedback<FEEDBACK>),
        (
            ActionClient<ClientResult, GOAL, FEEDBACK, RESULT, E1, E2>,
            Feedback<FEEDBACK>,
        ),
    > {
        let (goal_client, subscriber, result_client) = self.split();

        let result = subscriber.recv().await;

        if matches!(
            result.data.status,
            GoalStatus::Accepted | GoalStatus::Executing | GoalStatus::Canceling
        ) {
            FeedbackOrResult::Feedback((
                Self {
                    goal_client,
                    subscriber,
                    result_client,
                    _phantom: PhantomData::default(),
                },
                result.data,
            ))
        } else {
            // Succeeded, Canceled, Aborted
            FeedbackOrResult::Result((
                ActionClient {
                    goal_client,
                    subscriber,
                    result_client,
                    _phantom: PhantomData::default(),
                },
                result.data,
            ))
        }
    }
}

impl<GOAL, FEEDBACK, RESULT, E1, E2> ActionClient<ClientResult, GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Send + Clone + 'static,
    RESULT: Send + 'static,
{
    pub async fn recv_result(
        self,
    ) -> (
        ActionClient<ClientGoal, GOAL, FEEDBACK, RESULT, E1, E2>,
        ActionResult<RESULT>,
    ) {
        let (goal_client, subscriber, result_client) = self.split();

        let result_client = result_client.sel2().await;
        let result_client = result_client.send(()).await;
        let (result_client, result) = result_client.recv().await;
        let result_client = result_client.zero();

        (
            ActionClient {
                goal_client,
                subscriber,
                result_client,
                _phantom: PhantomData::default(),
            },
            result,
        )
    }
}

pub struct ServerRecvGoal; // RecvGoal state.
pub struct ServerFeedback; // Feedback state.

type GoalServerRecv<GOAL, E1> = S::Chan<(GoalSrvInner<GOAL>, E1), GoalSrvInner<GOAL>>;
type GoalServerSend<GOAL, E1> =
    S::Chan<(GoalSrvInner<GOAL>, E1), S::Send<GoalResponse, S::Var<S::Z>>>;
type ResultServer<RESULT, E2> = S::Chan<(ResultSrvInner<RESULT>, E2), ResultSrvInner<RESULT>>;

#[must_use]
pub struct ActionServer<STATE, GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Send + Clone + 'static,
{
    goal_server: GoalServerRecv<GOAL, E1>,
    publisher: Publisher<Feedback<FEEDBACK>>,
    result_server: ResultServer<RESULT, E2>,
    _phantom: PhantomData<STATE>,
}

impl<GOAL, FEEDBACK, RESULT, E1, E2> ActionServer<ServerRecvGoal, GOAL, FEEDBACK, RESULT, E1, E2>
where
    GOAL: Send + 'static,
    FEEDBACK: Send + Clone + 'static,
{
    pub async fn recv_goal(
        self,
    ) -> Result<
        (
            ActionServerGoalResponse<GOAL, FEEDBACK, RESULT, E1, E2>,
            GOAL,
        ),
        &'static str,
    > {
        let (goal_server, publisher, result_server) =
            (self.goal_server, self.publisher, self.result_server);

        offer! {goal_server,
            CLOSE => {
                goal_server.close();
                Err("connection closed")
            },
            GOAL => {
                let (goal_server, goal) = goal_server.recv().await;
                Ok((ActionServerGoalResponse {
                    goal_server,
                    publisher,
                    result_server
                }, goal))
            }
        }
    }
}

#[must_use]
pub struct ActionServerGoalResponse<GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Send + Clone + 'static,
{
    goal_server: GoalServerSend<GOAL, E1>,
    publisher: Publisher<Feedback<FEEDBACK>>,
    result_server: ResultServer<RESULT, E2>,
}

impl<GOAL, FEEDBACK, RESULT, E1, E2> ActionServerGoalResponse<GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Sync + Send + Clone + 'static,
{
    pub async fn reject(self) -> ActionServer<ServerRecvGoal, GOAL, FEEDBACK, RESULT, E1, E2> {
        let (goal_server, publisher, result_server) =
            (self.goal_server, self.publisher, self.result_server);

        let goal_server = goal_server.send(GoalResponse::Reject).await.zero();

        ActionServer {
            goal_server,
            publisher,
            result_server,
            _phantom: PhantomData::default(),
        }
    }

    async fn accept(
        self,
        response: GoalResponse,
        feedback: FEEDBACK,
    ) -> ActionServer<ServerFeedback, GOAL, FEEDBACK, RESULT, E1, E2> {
        let (goal_server, publisher, result_server) =
            (self.goal_server, self.publisher, self.result_server);

        let goal_server = goal_server.send(response).await.zero();
        publisher
            .send(Feedback {
                status: GoalStatus::Accepted,
                value: feedback,
            })
            .await;

        ActionServer {
            goal_server,
            publisher,
            result_server,
            _phantom: PhantomData::default(),
        }
    }

    pub async fn accept_and_execute(
        self,
        feedback: FEEDBACK,
    ) -> ActionServer<ServerFeedback, GOAL, FEEDBACK, RESULT, E1, E2> {
        self.accept(GoalResponse::AcceptAndExecute, feedback).await
    }

    pub async fn accept_and_defer(
        self,
        feedback: FEEDBACK,
    ) -> ActionServer<ServerFeedback, GOAL, FEEDBACK, RESULT, E1, E2> {
        self.accept(GoalResponse::AcceptAndDefer, feedback).await
    }
}

impl<GOAL, FEEDBACK, RESULT, E1, E2> ActionServer<ServerFeedback, GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Send + Sync + Clone + 'static,
{
    pub async fn send_feedback(
        self,
        status: GoalStatus,
        value: FEEDBACK,
    ) -> FeedbackOrResult<Self, ActionServerResult<GOAL, FEEDBACK, RESULT, E1, E2>> {
        let data = Feedback {
            status: status.clone(),
            value,
        };
        self.publisher.send(data).await;

        let (goal_server, publisher, result_server) =
            (self.goal_server, self.publisher, self.result_server);

        if matches!(
            status,
            GoalStatus::Accepted | GoalStatus::Executing | GoalStatus::Canceling
        ) {
            FeedbackOrResult::Feedback(Self {
                goal_server,
                publisher,
                result_server,
                _phantom: PhantomData::default(),
            })
        } else {
            // Succeeded, Canceled, Aborted
            FeedbackOrResult::Result(ActionServerResult {
                goal_server,
                publisher,
                result_server,
            })
        }
    }
}

#[must_use]
pub struct ActionServerResult<GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Send + Clone + 'static,
{
    goal_server: GoalServerRecv<GOAL, E1>,
    publisher: Publisher<Feedback<FEEDBACK>>,
    result_server: ResultServer<RESULT, E2>,
}

impl<GOAL, FEEDBACK, RESULT, E1, E2> ActionServerResult<GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Send + Sync + Clone + 'static,
    RESULT: Send + 'static,
{
    pub async fn send_result(
        self,
        status: ResultStatus,
        value: RESULT,
    ) -> ActionServer<ServerRecvGoal, GOAL, FEEDBACK, RESULT, E1, E2> {
        let (goal_server, publisher, result_server) =
            (self.goal_server, self.publisher, self.result_server);

        offer! {result_server,
            END => {
                result_server.close();
                unreachable!()
            },
            RECV => {
                let (result_server, _) =  result_server.recv().await;
                let result_server = result_server.send(ActionResult { status, value }).await;
                let result_server = result_server.zero();

                ActionServer {
                    goal_server,
                    publisher,
                    result_server,
                    _phantom: PhantomData::default()
                }
            }
        }
    }
}
