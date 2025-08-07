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

- [cpu_waking_to_active_cpu0_edge_irq0.md](cpu_waking_to_active_cpu0_edge_irq0.md)
- [cpu_waking_to_active_cpu0_edge_irq1.md](cpu_waking_to_active_cpu0_edge_irq1.md)
- [cpu_waking_to_active_cpu0_edge_irq2.md](cpu_waking_to_active_cpu0_edge_irq2.md)
- [cpu_waking_to_active_cpu0_edge_irq3.md](cpu_waking_to_active_cpu0_edge_irq3.md)
- [cpu_waking_to_active_cpu0_level_irq0.md](cpu_waking_to_active_cpu0_level_irq0.md)
- [cpu_waking_to_active_cpu0_level_irq1.md](cpu_waking_to_active_cpu0_level_irq1.md)
- [cpu_waking_to_active_cpu0_level_irq2.md](cpu_waking_to_active_cpu0_level_irq2.md)
- [cpu_waking_to_active_cpu0_level_irq3.md](cpu_waking_to_active_cpu0_level_irq3.md)
- [cpu_waking_to_active_cpu1_edge_irq0.md](cpu_waking_to_active_cpu1_edge_irq0.md)
- [cpu_waking_to_active_cpu1_edge_irq1.md](cpu_waking_to_active_cpu1_edge_irq1.md)
- [cpu_waking_to_active_cpu1_edge_irq2.md](cpu_waking_to_active_cpu1_edge_irq2.md)
- [cpu_waking_to_active_cpu1_edge_irq3.md](cpu_waking_to_active_cpu1_edge_irq3.md)
- [cpu_waking_to_active_cpu1_level_irq0.md](cpu_waking_to_active_cpu1_level_irq0.md)
- [cpu_waking_to_active_cpu1_level_irq1.md](cpu_waking_to_active_cpu1_level_irq1.md)
- [cpu_waking_to_active_cpu1_level_irq2.md](cpu_waking_to_active_cpu1_level_irq2.md)
- [cpu_waking_to_active_cpu1_level_irq3.md](cpu_waking_to_active_cpu1_level_irq3.md)
- [eventually_execute_edge_irq0.md](eventually_execute_edge_irq0.md)
- [eventually_execute_edge_irq1.md](eventually_execute_edge_irq1.md)
- [eventually_execute_edge_irq2.md](eventually_execute_edge_irq2.md)
- [eventually_execute_edge_irq3.md](eventually_execute_edge_irq3.md)
- [eventually_execute_level_irq0.md](eventually_execute_level_irq0.md)
- [eventually_execute_level_irq1.md](eventually_execute_level_irq1.md)
- [eventually_execute_level_irq2.md](eventually_execute_level_irq2.md)
- [eventually_execute_level_irq3.md](eventually_execute_level_irq3.md)
- [concurrent_work_conservation_edge_irq0.md](concurrent_work_conservation_edge_irq0.md)
- [concurrent_work_conservation_edge_irq1.md](concurrent_work_conservation_edge_irq1.md)
- [concurrent_work_conservation_edge_irq2.md](concurrent_work_conservation_edge_irq2.md)
- [concurrent_work_conservation_edge_irq3.md](concurrent_work_conservation_edge_irq3.md)
- [concurrent_work_conservation_level_irq0.md](concurrent_work_conservation_level_irq0.md)
- [concurrent_work_conservation_level_irq1.md](concurrent_work_conservation_level_irq1.md)
- [concurrent_work_conservation_level_irq2.md](concurrent_work_conservation_level_irq2.md)
- [concurrent_work_conservation_level_irq3.md](concurrent_work_conservation_level_irq3.md)
