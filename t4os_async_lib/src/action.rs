use core::marker::PhantomData;

use crate::{
    pubsub::{Publisher, Subscriber},
    session_types,
};
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
pub struct Feedback<T> {
    pub status: GoalStatus,
    pub value: T,
}

#[derive(Clone)]
pub struct ActionResult<T> {
    status: ResultStatus,
    value: T,
}

type GoalSrvInner<T> = S::Offer<S::Eps, S::Recv<T, S::Send<GoalResponse, S::Var<S::Z>>>>;
type GoalCliInner<T> = <GoalSrvInner<T> as S::HasDual>::Dual;
type GoalSrv<T> = S::Rec<GoalSrvInner<T>>;
type GoalCli<T> = S::Rec<GoalCliInner<T>>;

type ResultSrvInner<T> = S::Offer<S::Eps, S::Recv<(), S::Send<ActionResult<T>, S::Var<S::Z>>>>;
type ResultCliInner<T> = <ResultSrvInner<T> as S::HasDual>::Dual;
type ResultSrv<T> = S::Rec<ResultSrvInner<T>>;
type ResultCli<T> = S::Rec<ResultCliInner<T>>;

pub struct ClientGoal; // Goal state.
pub struct ClientFeedback; // Feedback state.
pub struct ClientResult; // ResultState

#[must_use]
pub enum FeedbackOrResult<T1, T2> {
    Feedback(T1),
    Result(T2),
}

#[must_use]
pub struct ActionClient<STATE, GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Clone + 'static,
{
    goal_client: S::Chan<(GoalCliInner<GOAL>, E1), GoalCliInner<GOAL>>,
    subscriber: Subscriber<Feedback<FEEDBACK>>,
    result_client: S::Chan<(ResultCliInner<RESULT>, E2), ResultCliInner<RESULT>>,
    _phantom: PhantomData<STATE>,
}

impl<GOAL, FEEDBACK, RESULT, E1, E2> ActionClient<ClientGoal, GOAL, FEEDBACK, RESULT, E1, E2>
where
    GOAL: Send + 'static,
    FEEDBACK: Clone + 'static,
{
    pub async fn send_goal(
        self,
        goal: GOAL,
    ) -> Result<
        ActionClient<ClientFeedback, GOAL, FEEDBACK, RESULT, E1, E2>,
        ActionClient<ClientGoal, GOAL, FEEDBACK, RESULT, E1, E2>,
    > {
        let (goal_client, subscriber, result_client) =
            (self.goal_client, self.subscriber, self.result_client);
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
        let (goal_client, result_client) = (self.goal_client, self.result_client);
        goal_client.sel1().await.close();
        result_client.sel1().await.close();
    }
}

impl<GOAL, FEEDBACK, RESULT, E1, E2> ActionClient<ClientFeedback, GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Clone + 'static,
{
    pub async fn recv_feedback(
        self,
    ) -> FeedbackOrResult<
        (
            ActionClient<ClientFeedback, GOAL, FEEDBACK, RESULT, E1, E2>,
            Feedback<FEEDBACK>,
        ),
        (
            ActionClient<ClientResult, GOAL, FEEDBACK, RESULT, E1, E2>,
            Feedback<FEEDBACK>,
        ),
    > {
        let (goal_client, subscriber, result_client) =
            (self.goal_client, self.subscriber, self.result_client);

        let result = subscriber.recv().await;

        if matches!(
            result.data.status,
            GoalStatus::Accepted | GoalStatus::Executing | GoalStatus::Canceling
        ) {
            FeedbackOrResult::Feedback((
                ActionClient {
                    goal_client,
                    subscriber,
                    result_client,
                    _phantom: PhantomData::default(),
                },
                result.data,
            ))
        } else {
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
    FEEDBACK: Clone + 'static,
    RESULT: Send + 'static,
{
    pub async fn recv_result(
        self,
    ) -> (
        ActionClient<ClientGoal, GOAL, FEEDBACK, RESULT, E1, E2>,
        ActionResult<RESULT>,
    ) {
        let (goal_client, subscriber, result_client) =
            (self.goal_client, self.subscriber, self.result_client);

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

#[must_use]
pub struct ActionServer<GOAL, FEEDBACK, RESULT, E1, E2>
where
    FEEDBACK: Clone + 'static,
{
    goal_server: S::Chan<(GoalSrvInner<GOAL>, E1), GoalSrvInner<GOAL>>,
    publisher: Publisher<FEEDBACK>,
    result_server: S::Chan<(ResultSrvInner<RESULT>, E2), ResultSrvInner<RESULT>>,
}
