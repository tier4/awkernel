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
Depth=     413 States=    1e+06 Transitions= 2.18e+06 Memory=   184.198 t=     0.56 R=   2e+06
Depth=     413 States=    2e+06 Transitions= 4.59e+06 Memory=   240.448 t=     1.18 R=   2e+06
Depth=     413 States=    3e+06 Transitions= 7.12e+06 Memory=   297.089 t=     1.85 R=   2e+06
Depth=     413 States=    4e+06 Transitions= 9.74e+06 Memory=   353.437 t=     2.52 R=   2e+06
Depth=     413 States=    5e+06 Transitions= 1.24e+07 Memory=   409.980 t=     3.22 R=   2e+06
Depth=     413 States=    6e+06 Transitions=  1.5e+07 Memory=   466.425 t=     3.88 R=   2e+06
Depth=     413 States=    7e+06 Transitions= 1.77e+07 Memory=   523.163 t=     4.59 R=   2e+06

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (fairness)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 128 byte, depth reached 413, errors: 0
  3662210 states, stored (7.32408e+06 visited)
 11323856 states, matched
 18647932 transitions (= visited+matched)
 16660624 atomic steps
hash conflicts:    808109 (resolved)

Stats on memory usage (in Megabytes):
  544.839       equivalent memory usage for states (stored*(State-vector + overhead))
  413.352       actual memory usage for states (compression: 75.87%)
                state-vector as stored = 90 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    0.534       memory used for DFS stack (-m10000)
  541.620       total actual memory usage



pan: elapsed time 4.84 seconds
pan: rate 1513238.8 states/second
```
