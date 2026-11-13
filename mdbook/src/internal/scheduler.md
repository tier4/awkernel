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
| `fn get_scheduler(sched_type: &SchedulerType)` | Get a scheduler.              |

`SchedulerType` is an enum for the scheduler type and defined in [awkernel_async_lib/src/scheduler.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler.rs) as follows.

```rust
pub enum SchedulerType {
    EDF(u64, CpuSet), // relative deadline and CPU affinity set
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
> edf.rs  panicked.rs  prioritized_fifo.rs  prioritized_rr.rs
```

A scheduler can be implemented by implementing `Scheduler` Trait.
Each scheduler must be registered in the following three locations.
`fn get_next_task()`, `fn get_scheduler(sched_type: &SchedulerType)` and `pub enum SchedulerType`.

### EDF Scheduler

The Earliest Deadline First (EDF) scheduler is implemented in [edf.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler/edf.rs). This scheduler restricts each task to a set of CPU cores (a cluster), specified as a `CpuSet` bitmask. A one-bit `CpuSet` pins a task to a single core (partitioned EDF), and `CpuSet::all()` lets it run on every worker core (global EDF).

The scheduler holds two affinity-aware priority queues, [`AffinityBTreeQueue`](https://crates.io/crates/affinity_btree_queue), each backed by an augmented B-tree. The global queue holds the tasks whose set holds every worker core, and the restricted queue holds the other tasks. Each entry carries `(priority, affinity, task)`, where the priority is `(absolute_deadline, wake_time, seq)`. Smaller values dequeue first, so tasks are ordered by earliest deadline with wake time as a tie-breaker. `seq` grows with each push, so tasks with equal deadlines and wake times dequeue in push order across both queues. Every B-tree node stores the OR of the affinities in its subtree, which lets `pop_for_cpu(cpu)` find the earliest-deadline task runnable on `cpu` in logarithmic time while skipping subtrees with no eligible entry.

When a task is enqueued via `wake_task()`, the scheduler reads the `SchedulerType::EDF(relative_deadline, cpu_set)` attached to the task and calculates the absolute deadline as `uptime + relative_deadline`. If the task is part of a DAG, `calculate_and_update_dag_deadline()` is used instead to propagate deadlines through the DAG. The task priority (`PriorityInfo`) becomes `MAX_TASK_PRIORITY - absolute_deadline`, so an earlier deadline gives a higher priority. The task is then pushed into the queue with its `cpu_set` as the affinity mask. Preemption is handled via `invoke_preemption()`. If the task is already running, the scheduler does nothing. If an idle core in the set will take the task, the scheduler only enqueues it. An idle core takes the earliest queued task runnable on it, so it takes the new task if the task is earlier than every queued task runnable on that core, or if the queue holds fewer tasks than the set has idle cores. Otherwise, the scheduler chooses the core running the lowest-priority task among the busy cores of the set. It sends an IPI to that core when the new task has a higher priority than the task running (or pending preemption) on it. Against another EDF task, a higher priority means an earlier deadline.

`get_next()` pops the earliest-deadline task of either queue whose `cpu_set` contains the calling CPU (`pop_for_cpu`), so a task is only ever dequeued by a core within its set. This guarantees CPU affinity. CPU 0 (the primary core) is always excluded from `cpu_set` when a task is spawned. The `cpu_set` is normalized at spawn time by removing CPU 0 and out-of-range bits; if this leaves the set empty (for example an empty set, or one naming only CPU 0 or out-of-range cores), the task is not rejected but falls back to all worker cores (`1..num_cpu()`) with a warning.

Bookkeeping for sleeping workers uses two pieces of state. A single global counter (`NUM_CLUSTERED_TASKS_IN_QUEUE`) tracks how many tasks are queued across all clustered schedulers; it is maintained by the `ClusteredTask` RAII wrapper (incremented on enqueue, decremented exactly once on dequeue or drop) and lets `get_next_task()` skip the clustered schedulers entirely when it is zero. `wake_workers()` reads the other information from the run queues through `Scheduler::queued_workers()` (summed over all clustered schedulers by `clustered_queued_workers()`). It wakes every core in the affinity mask of the restricted queue, which its B-tree root maintains (`affinity_mask()`, O(1)). For the global queue, it wakes only one sleeping core per queued task, as it does for the tasks of the other schedulers. With a single queue, one queued task that every worker can run would put every worker in the mask and wake all of them.

A new clustered scheduler must (1) wrap its queue entries in `ClusteredTask`, (2) implement `Scheduler::queued_workers()`, and (3) be placed in the clustered prefix of `PRIORITY_LIST` and matched by `SchedulerType::is_clustered()`; the prefix requirement is enforced at compile time.

### PrioritizedFIFO Scheduler

The PrioritizedFIFO scheduler is implemented in [prioritized_fifo.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler/prioritized_fifo.rs). This scheduler provides fixed-priority scheduling where tasks are executed in First-In-First-Out order within each priority level.

The scheduler uses a `PriorityQueue<PrioritizedFIFOTask>` as its run queue. When a task is enqueued through `wake_task()`, the priority is extracted from `SchedulerType::PrioritizedFIFO(priority)` and used to insert the task into the priority queue. The get_next() method retrieves the task at the head of the highest-priority non-empty queue.

The scheduler implements preemption via `invoke_preemption()`, which evaluates all currently running tasks and determines if the newly awakened task should preempt any of them. If preemption is triggered, the scheduler sends an IPI to the target CPU and updates the preemption pending queue. Preemption requires a strictly higher priority (`Task::preempts()`): a task woken while an equal-priority task is running is enqueued behind it, so the FIFO order within a priority level also holds against running tasks. The same rule applies to the other schedulers and to the preemption handler itself, which re-queues a pending task if the task running on the target CPU no longer has a strictly lower priority, except for the PrioritizedRR time-quantum rotation described below.

### PrioritizedRR Scheduler

The PrioritizedRR (Prioritized Round Robin) scheduler is implemented in [prioritized_rr.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler/prioritized_rr.rs). This scheduler combines fixed-priority scheduling with time quantum enforcement to provide fair CPU time distribution.

The scheduler maintains a `PriorityQueue<PrioritizedRRTask>` similar to PrioritizedFIFO, but adds time quantum management with a default interval of 4ms (4,000 microseconds). The scheduler provides two preemption mechanisms: `invoke_preemption_wake()` for priority-based preemption when tasks are awakened, and `invoke_preemption_tick()` for time quantum-based preemption.

The `invoke_preemption_tick()` method is called periodically on primary CPU to check if the currently running task has exceeded its time quantum. It compares the elapsed execution time against the configured interval and triggers preemption by sending an IPI if the quantum is exceeded. The task pushed by the tick usually has the same priority as the running one; `do_preemption()` lets such an equal-priority pending task preempt a running PrioritizedRR task, which is the only case where equal priority preempts.

### Panicked Scheduler

The Panicked scheduler is implemented in [panicked.rs](https://github.com/tier4/awkernel/blob/main/awkernel_async_lib/src/scheduler/panicked.rs). This scheduler handles tasks that have entered a panicked state and provides them with the lowest scheduling priority in the system. The scheduler uses a simple `VecDeque<Arc<Task>>` as its run queue, implementing basic FIFO ordering without any priority considerations.
