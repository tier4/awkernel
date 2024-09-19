# Scheduler

Scheduler is a trait for the scheduler and defined in [awkernel_async_lib/src/scheduler.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler.rs) as follows.

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

|  function             | description |
|-----------------------|-------------------------------|
| `fn get_next_task()`  | Get the next executable task.  |
| `fn get_scheduler(sched_type: SchedulerType)` | Get a scheduler.  |

The `SchedulerType` is an enum for the scheduler type and defined in [awkernel_async_lib/src/scheduler.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler.rs) as follows.

```rust
pub enum SchedulerType {
    FIFO,

    PrioritizedFIFO(u8),

    RR,

    Panicked,
}
```

## SleepingTasks

The `SleepingTasks` is a struct for managing sleeping tasks and defined in [awkernel_async_lib/src/scheduler.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler.rs) as follows.

```rust
struct SleepingTasks {
    delta_list: DeltaList<Box<dyn FnOnce() + Send>>,
    base_time: u64,
}
```

The `SleepingTasks` struct has the following functions.

|  function             | description |
|-----------------------|-------------|
| `fn new()` | Create a new `SleepingTasks` instance. |
| `fn sleep_task(&mut self, handler: Box<dyn FnOnce() + Send>, mut dur: u64)` | Sleep a task for a certain duration. |
| `fn wake_task(&mut self)` | Wake up tasks after sleep. |

## Implementing a Scheduler

The scheduler is implemented under the folder [awkernel_async_lib/src/scheduler](https://github.com/tier4/awkernel/tree/main/awkernel_async_lib/src/scheduler).

```shell
$ ls awkernel_async_lib/src/scheduler
> fifo.rs  panicked.rs  prioritized_fifo.rs  rr.rs
```

Scheduler implementation is done by implementing Scheduler Trait.
When implementing a scheduler, it is necessary to register it in the following three places.
`fn get_next_task()`, `fn get_scheduler(sched_type: SchedulerType)` and `pub enum SchedulerType`.

