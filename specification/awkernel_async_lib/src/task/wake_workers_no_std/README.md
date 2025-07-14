# Sleep and Notification

This is the no_std version of [wake_workers](../wake_workers).

In `run_main()` function of `awkernel_async_lib`,
worker threads will sleep until a task is woken up.
In such case, the worker threads must be woken up to execute the task.
To achieve this, Awkernel implements `awkernel_lib::cpu::sleep_cpu()` and
`awkernel_async_lib::task::wake_workers()`.

This is a model of the above implementation.
We prepare `WORKERS` worker threads and `WORKERS + 1` tasks in this model.
To test notification works correctly,
we prepare up to `WORKERS - 1` blocking tasks.

For example, if `WORKERS` is 3, two worker threads will be blocked
but one worker thread will execute tasks as follows.

1. worker thread 3: execute and block
2. worker thread 1: execute and block
3. worker thread 2: sleep
4. a task becomes ready to run
5. primary CPU: wake up worker thread 1
6. worker thread 1: execute a task

## Targets

- [awkernel_lib/src/cpu/sleep_cpu_no_std.rs](../../../../../awkernel_lib/src/cpu/sleep_cpu_no_std.rs).
- [awkernel_lib/src/interrupt.rs](../../../../../awkernel_lib/src/interrupt.rs).
- [awkernel_async_lib/src/task.rs](../../../../../awkernel_async_lib/src/task.rs).
- [kernel/src/main.rs](../../../../../kernel/src/main.rs).

## Subjects to be Verified

1. When tasks are more than workers, all tasks will be eventually executes.
2. When CPU is woken up, it will wake up eventually.
3. Concurrent work conservation is maintained.
  - B. Lepers, et al. Provable Multicore Schedulers with Ipanema: Application to Work Conservation, EuroSys 2020

## Results

- W2A_CPU0_E: [cpu_waking_to_active_cpu0_edge.md](cpu_waking_to_active_cpu0_edge.md)
- W2A_CPU0_L: [cpu_waking_to_active_cpu0_level.md](cpu_waking_to_active_cpu0_level.md)
- W2A_CPU1_E: [cpu_waking_to_active_cpu1_edge.md](cpu_waking_to_active_cpu1_edge.md)
- W2A_CPU1_L: [cpu_waking_to_active_cpu1_level.md](cpu_waking_to_active_cpu1_level.md)
- EV_EXEC_E: [eventually_execute_edge.md](eventually_execute_edge.md)
- EV_EXEC_L: [eventually_execute_level.md](eventually_execute_level.md)
- CWC_E:[concurrent_work_conservation_edge.md](concurrent_work_conservation_edge.md)
- CWC_L: [concurrent_work_conservation_level.md](concurrent_work_conservation_level.md)

| | W2A_CPU0_E | W2A_CPU0_L | W2A_CPU1_E | W2A_CPU1_L | EV_EXEC_E | EV_EXEC_L | CWC_E | CWC_L |
|---|---|---|---|---|---|---|---|---|
| time (s) | 1360 | 1400 | 1290 | 1310 | 1800 | 1870 | 687 | 644 |
| memory (GiB) | 52.0 | 52.9 | 49.7 | 50.5 | 51.8 | 52.7 | 29.0 | 29.6 |
