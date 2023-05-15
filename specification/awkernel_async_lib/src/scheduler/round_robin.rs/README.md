# Round Robin Scheduler

## Target

- [awkernel_async_lib/src/scheduler/round_robin.rs](../../../../../awkernel_async_lib/src/scheduler/round_robin.rs).

## Subjects to be Verified

1. The scheduler is deadlock- and starvation-free.
2. If a task is in a state, the task is not in other states at the same time.

## Result

![result](result.png)

## Detail

### States

States are represented as follows.

```
\* awkernel_async_lib::task::State
StateInQueue = {};
StateReady = 1..TASK_NUM;
StateRunning = {};
StateWaiting = {};
```

If the task 1 is `StateReady`, then $1 \in StateReady$.

## Starvation-free

The starvation-free can be verified as follows.

$$
\forall x \in 1..\mathrm{TASK\_NUM}:
    (x \in StateInQueue \leadsto x \in StateRunning)
$$
