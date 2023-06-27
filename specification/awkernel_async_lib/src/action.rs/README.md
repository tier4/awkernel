# Action Server and Client

The protocol of action server can be defined by session types as follows.
`G`, `F`, and `R` stand for the types of goal, feedback, and result, respectively.

```rust
type ProtoServer<G, F, R> = S::Rec<ProtoServerInn<G, F, R>>;
type ProtoServerInn<G, F, R> = S::Offer<S::Eps /* Close. */, ProtoServerGoal<G, F, R>>;
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
    ResultStatus<R>, /* Send a result. */
    S::Var<S::Z>,    /* Goto ProtoServerInn. */
>;
```

The protocol of action client is dual of this.

The protocol can be described in sequence diagram as follows.

```mermaid
sequenceDiagram
    loop
        alt
            Client->>Server: close
            Note over Client,Server: break loop
        else
            Client->>Server: goal
            alt
                Server->>Client: reject
            else
                Server->>Client: accept
                Server->>Client: goal response
                Client->>Server: attribute
                Server->>Client: Receiver (endpoint)

                loop
                    alt
                        Sender (Server)->>Receiver (Client): feedback
                    else
                        Note over Sender (Server),Receiver (Client): break loop
                    end
                end

                Server->>Client: status and result
            end
        end
    end
```

## State Machine of Server

The state machine of action server is as follows.
This can be described by [action_server.tla](./action_server.tla) in TLA+.

```mermaid
stateDiagram
    [*] --> ServerRecvGoal
    ServerRecvGoal --> [*]: close
    ServerRecvGoal --> ServerSendGoalResult: recv_goal
    ServerSendGoalResult --> ServerRecvGoal: reject
    ServerSendGoalResult --> ServerSendFeedback: accept
    ServerSendFeedback --> ServerSendFeedback: send_feedback
    ServerSendFeedback --> ServerRecvGoal: send_result
    ServerSendFeedback --> ServerSendCancel: send_feedback (cancel)
    ServerSendCancel --> ServerRecvGoal: send_cancel
```

## State Machine of Client

The state machine of action client is as follows.
This can be described by [action_client.tla](./action_client.tla) in TLA+.

```mermaid
stateDiagram
    [*] --> ClientSendGoal
    ClientSendGoal --> [*]: close
    ClientSendGoal --> ClientRecvFeedback: accept
    ClientSendGoal --> ClientSendGoal: reject
    ClientRecvFeedback --> ClientRecvFeedback: recv feedback
    ClientRecvFeedback --> ClientSendGoal: recv result
```
