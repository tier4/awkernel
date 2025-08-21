# Scheduler

`Scheduler` is a trait for the scheduler and defined in [awkernel_async_lib/src/scheduler.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler.rs) as follows.

```rust
pub(crate) trait Scheduler {
    /// Enqueue an executable task.
    /// The enqueued task will be taken by `get_next()`.
    fn wake_task(&self, task: Arc<Task>);

    /// Get the next executable task.
    fn get_next(&self) -> Option<Arc<Task>>;

    /// Get the scheduler name.
    fn scheduler_name(&self) -> SchedulerType;

    #[allow(dead_code)] // TODO: to be removed
    fn priority(&self) -> u8;
}
```

There are several functions regarding the scheduler in [awkernel_async_lib/src/scheduler.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler.rs).

| function                                      | description                   |
| --------------------------------------------- | ----------------------------- |
| `fn get_next_task()`                          | Get the next executable task. |
| `fn get_scheduler(sched_type: SchedulerType)` | Get a scheduler.              |

`SchedulerType` is an enum for the scheduler type and defined in [awkernel_async_lib/src/scheduler.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler.rs) as follows.

```rust
pub enum SchedulerType {
    GEDF(u64), // relative deadline
    PrioritizedFIFO(u8),
    PrioritizedRR(u8),
    Panicked,
}
```

## SleepingTasks

`SleepingTasks` is a struct for managing sleeping tasks and defined in [awkernel_async_lib/src/scheduler.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler.rs) as follows.

```rust
struct SleepingTasks {
    delta_list: DeltaList<Box<dyn FnOnce() + Send>>,
    base_time: u64,
}
```

`SleepingTasks` struct has the following functions.

| function                                                                    | description                            |
| --------------------------------------------------------------------------- | -------------------------------------- |
| `fn new()`                                                                  | Create a new `SleepingTasks` instance. |
| `fn sleep_task(&mut self, handler: Box<dyn FnOnce() + Send>, mut dur: u64)` | Sleep a task for a certain duration.   |
| `fn wake_task(&mut self)`                                                   | Wake up tasks after sleep.             |

## Scheduler Implementation

Some schedulers are implemented under the folder [awkernel_async_lib/src/scheduler](https://github.com/tier4/awkernel/tree/main/awkernel_async_lib/src/scheduler).

```shell
$ ls awkernel_async_lib/src/scheduler
> gedf.rs  panicked.rs  prioritized_fifo.rs  prioritized_rr.rs
```

A scheduler can be implemented by implementing `Scheduler` Trait.
Each scheduler must be registered in the following three locations.
`fn get_next_task()`, `fn get_scheduler(sched_type: SchedulerType)` and `pub enum SchedulerType`.

### GEDF Scheduler

The Global Earliest Deadline First (GEDF) scheduler is implemented in [gedf.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler/gedf.rs). This scheduler implements a real-time scheduling algorithm that prioritizes tasks based on their absolute deadlines.

The scheduler maintains a `BinaryHeap<GEDFTask>` as its run queue, where tasks are ordered by their absolute deadlines. When a task is enqueued via `wake_task()`, the scheduler calculates the absolute deadline by adding the relative deadline (specified in `SchedulerType::GEDF(relative_deadline)`) to the current uptime. The task's priority is updated using `MAX_TASK_PRIORITY - absolute_deadline` to ensure proper inter-scheduler priority comparison.

The `GEDFTask` struct implements custom ordering where tasks are compared first by absolute deadline (earlier deadlines have higher priority), and then by wake time for tie-breaking. The scheduler supports preemption through the `invoke_preemption()` method, which sends IPIs to target CPUs when a task with an earlier deadline arrives and can preempt currently running tasks.

### PrioritizedFIFO Scheduler

The PrioritizedFIFO scheduler is implemented in [prioritized_fifo.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler/prioritized_fifo.rs). This scheduler provides fixed-priority scheduling where tasks are executed in First-In-First-Out order within each priority level.

The scheduler uses a `PriorityQueue<PrioritizedFIFOTask>` as its run queue. When a task is enqueued through `wake_task()`, the priority is extracted from `SchedulerType::PrioritizedFIFO(priority)` and used to insert the task into the priority queue. Tasks with higher priority values are selected first by `get_next()`.

The scheduler implements preemption via `invoke_preemption()`, which evaluates all currently running tasks and determines if the newly awakened task should preempt any of them. If preemption is triggered, the scheduler sends an IPI to the target CPU and updates the preemption pending queue.

### PrioritizedRR Scheduler

The PrioritizedRR (Prioritized Round Robin) scheduler is implemented in [prioritized_rr.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler/prioritized_rr.rs). This scheduler combines fixed-priority scheduling with time quantum enforcement to provide fair CPU time distribution.

The scheduler maintains a `PriorityQueue<PrioritizedRRTask>` similar to PrioritizedFIFO, but adds time quantum management with a default interval of 4ms (4,000 microseconds). The scheduler provides two preemption mechanisms: `invoke_preemption_wake()` for priority-based preemption when tasks are awakened, and `invoke_preemption_tick()` for time quantum-based preemption.

The `invoke_preemption_tick()` method is called periodically on primary CPU to check if the currently running task has exceeded its time quantum. It compares the elapsed execution time against the configured interval and triggers preemption by sending an IPI if the quantum is exceeded.

### Panicked Scheduler

The Panicked scheduler is implemented in [panicked.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler/panicked.rs). This scheduler handles tasks that have entered a panicked state and provides them with the lowest scheduling priority in the system. The scheduler uses a simple `VecDeque<Arc<Task>>` as its run queue, implementing basic FIFO ordering without any priority considerations.
