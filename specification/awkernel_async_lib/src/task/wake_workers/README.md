# Sleep and Notification

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

- [awkernel_lib/src/cpu/sleep_cpu_std.rs](../../../../../awkernel_lib/src/cpu/sleep_cpu_std.rs).
- [awkernel_async_lib/src/task.rs](../../../../../awkernel_async_lib/src/task.rs).
- [kernel/src/main.rs](../../../../../kernel/src/main.rs).

## Subjects to be Verified

1. When tasks are more than workers, all tasks will be eventually executes.

## Result

```
$ make run
rm -f *.trail
./pan -a -n
Depth=     661 States=    1e+06 Transitions=  1.7e+06 Memory=   180.390 t=     0.43 R=   2e+06
Depth=     661 States=    2e+06 Transitions= 3.98e+06 Memory=   232.831 t=     0.94 R=   2e+06
Depth=     819 States=    3e+06 Transitions= 6.06e+06 Memory=   285.272 t=     1.45 R=   2e+06
Depth=     819 States=    4e+06 Transitions= 8.22e+06 Memory=   337.616 t=     1.96 R=   2e+06
Depth=     819 States=    5e+06 Transitions= 1.06e+07 Memory=   389.960 t=      2.5 R=   2e+06
Depth=     819 States=    6e+06 Transitions=  1.3e+07 Memory=   442.890 t=     3.06 R=   2e+06
Depth=     819 States=    7e+06 Transitions= 1.55e+07 Memory=   496.405 t=     3.62 R=   2e+06
Depth=     819 States=    8e+06 Transitions= 1.77e+07 Memory=   547.675 t=     4.15 R=   2e+06
Depth=     819 States=    9e+06 Transitions=    2e+07 Memory=   600.409 t=     4.71 R=   2e+06
Depth=     819 States=    1e+07 Transitions= 2.25e+07 Memory=   653.046 t=     5.29 R=   2e+06
Depth=     819 States=  1.1e+07 Transitions= 2.49e+07 Memory=   705.487 t=     5.85 R=   2e+06
Depth=     819 States=  1.2e+07 Transitions= 2.73e+07 Memory=   758.515 t=     6.43 R=   2e+06
Depth=     819 States=  1.3e+07 Transitions= 2.98e+07 Memory=   811.347 t=     7.03 R=   2e+06

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (eventually_execute)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 120 byte, depth reached 819, errors: 0
  6618195 states, stored (1.32346e+07 visited)
 17113256 states, matched
 30347874 transitions (= visited+matched)
   433324 atomic steps
hash conflicts:   2424159 (resolved)

Stats on memory usage (in Megabytes):
  934.117       equivalent memory usage for states (stored*(State-vector + overhead))
  695.595       actual memory usage for states (compression: 74.47%)
                state-vector as stored = 82 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    0.534       memory used for DFS stack (-m10000)
  823.749       total actual memory usage



pan: elapsed time 7.16 seconds
pan: rate 1848410.3 states/second
```
