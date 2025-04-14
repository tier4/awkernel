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
Depth=     349 States=    1e+06 Transitions= 1.73e+06 Memory=   187.714 t=     0.45 R=   2e+06
Depth=     349 States=    2e+06 Transitions= 3.37e+06 Memory=   239.960 t=     0.92 R=   2e+06
Depth=     471 States=    3e+06 Transitions= 5.65e+06 Memory=   294.940 t=     1.46 R=   2e+06
Depth=     471 States=    4e+06 Transitions= 8.14e+06 Memory=   350.702 t=     2.03 R=   2e+06
Depth=     471 States=    5e+06 Transitions= 1.07e+07 Memory=   408.417 t=     2.64 R=   2e+06
Depth=     471 States=    6e+06 Transitions= 1.33e+07 Memory=   463.690 t=     3.25 R=   2e+06
Depth=     471 States=    7e+06 Transitions= 1.57e+07 Memory=   519.452 t=     3.82 R=   2e+06
Depth=     471 States=    8e+06 Transitions= 1.78e+07 Memory=   576.483 t=      4.4 R=   2e+06
Depth=     471 States=    9e+06 Transitions= 2.01e+07 Memory=   632.636 t=     4.98 R=   2e+06
Depth=     471 States=    1e+07 Transitions= 2.24e+07 Memory=   688.886 t=     5.58 R=   2e+06
Depth=     471 States=  1.1e+07 Transitions= 2.51e+07 Memory=   744.745 t=     6.21 R=   2e+06
Depth=     471 States=  1.2e+07 Transitions= 2.78e+07 Memory=   801.093 t=     6.86 R=   2e+06
Depth=     471 States=  1.3e+07 Transitions= 3.05e+07 Memory=   858.026 t=     7.51 R=   2e+06
Depth=     471 States=  1.4e+07 Transitions= 3.32e+07 Memory=   914.569 t=     8.16 R=   2e+06
Depth=     471 States=  1.5e+07 Transitions= 3.58e+07 Memory=   971.112 t=      8.8 R=   2e+06
Depth=     471 States=  1.6e+07 Transitions= 3.85e+07 Memory=  1027.167 t=     9.49 R=   2e+06
Depth=     471 States=  1.7e+07 Transitions= 4.13e+07 Memory=  1084.491 t=     10.2 R=   2e+06
Depth=     471 States=  1.8e+07 Transitions= 4.36e+07 Memory=  1142.011 t=     10.8 R=   2e+06
Depth=     471 States=  1.9e+07 Transitions= 4.59e+07 Memory=  1197.968 t=     11.5 R=   2e+06
Depth=     471 States=    2e+07 Transitions= 4.85e+07 Memory=  1254.413 t=     12.1 R=   2e+06
Depth=     471 States=  2.1e+07 Transitions=  5.1e+07 Memory=  1311.151 t=     12.8 R=   2e+06
Depth=     471 States=  2.2e+07 Transitions= 5.35e+07 Memory=  1367.304 t=     13.5 R=   2e+06
Depth=     471 States=  2.3e+07 Transitions= 5.62e+07 Memory=  1423.261 t=     14.2 R=   2e+06
Depth=     471 States=  2.4e+07 Transitions=  5.9e+07 Memory=  1480.097 t=     14.9 R=   2e+06
Depth=     471 States=  2.5e+07 Transitions= 6.18e+07 Memory=  1536.347 t=     15.6 R=   2e+06
Depth=     471 States=  2.6e+07 Transitions= 6.46e+07 Memory=  1593.085 t=     16.3 R=   2e+06
Depth=     471 States=  2.7e+07 Transitions= 6.72e+07 Memory=  1650.019 t=       17 R=   2e+06
Depth=     471 States=  2.8e+07 Transitions=    7e+07 Memory=  1706.855 t=     17.7 R=   2e+06
Depth=     471 States=  2.9e+07 Transitions= 7.28e+07 Memory=  1763.397 t=     18.4 R=   2e+06
Depth=     471 States=    3e+07 Transitions= 7.55e+07 Memory=  1819.355 t=     19.2 R=   2e+06
Depth=     471 States=  3.1e+07 Transitions= 7.82e+07 Memory=  1876.093 t=     19.9 R=   2e+06
Depth=     471 States=  3.2e+07 Transitions= 8.08e+07 Memory=  1932.733 t=     20.6 R=   2e+06
Depth=     471 States=  3.3e+07 Transitions= 8.37e+07 Memory=  1991.913 t=     21.4 R=   2e+06
Depth=     471 States=  3.4e+07 Transitions= 8.62e+07 Memory=  2045.819 t=     22.1 R=   2e+06
pan: resizing hashtable to -w26..  done
Depth=     471 States=  3.5e+07 Transitions= 8.88e+07 Memory=  2598.933 t=     23.6 R=   1e+06
Depth=     471 States=  3.6e+07 Transitions= 9.13e+07 Memory=  2654.890 t=     24.2 R=   1e+06
Depth=     471 States=  3.7e+07 Transitions= 9.39e+07 Memory=  2711.823 t=     24.9 R=   1e+06
Depth=     471 States=  3.8e+07 Transitions= 9.67e+07 Memory=  2768.366 t=     25.6 R=   1e+06
Depth=     471 States=  3.9e+07 Transitions= 9.94e+07 Memory=  2824.421 t=     26.2 R=   1e+06
Depth=     471 States=    4e+07 Transitions= 1.02e+08 Memory=  2880.964 t=     26.9 R=   1e+06
Depth=     471 States=  4.1e+07 Transitions= 1.05e+08 Memory=  2937.995 t=     27.6 R=   1e+06
Depth=     471 States=  4.2e+07 Transitions= 1.08e+08 Memory=  2994.831 t=     28.2 R=   1e+06
Depth=     471 States=  4.3e+07 Transitions= 1.11e+08 Memory=  3051.179 t=     28.9 R=   1e+06
Depth=     471 States=  4.4e+07 Transitions= 1.13e+08 Memory=  3108.112 t=     29.5 R=   1e+06
Depth=     471 States=  4.5e+07 Transitions= 1.16e+08 Memory=  3164.948 t=     30.2 R=   1e+06
Depth=     471 States=  4.6e+07 Transitions= 1.19e+08 Memory=  3221.784 t=     30.9 R=   1e+06
Depth=     471 States=  4.7e+07 Transitions= 1.22e+08 Memory=  3278.522 t=     31.5 R=   1e+06
Depth=     471 States=  4.8e+07 Transitions= 1.24e+08 Memory=  3335.163 t=     32.2 R=   1e+06
Depth=     471 States=  4.9e+07 Transitions= 1.27e+08 Memory=  3391.706 t=     32.9 R=   1e+06
Depth=     471 States=    5e+07 Transitions=  1.3e+08 Memory=  3448.542 t=     33.6 R=   1e+06
Depth=     471 States=  5.1e+07 Transitions= 1.33e+08 Memory=  3505.183 t=     34.3 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (eventually_execute)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 128 byte, depth reached 471, errors: 0
 25809093 states, stored (5.16126e+07 visited)
 82762336 states, matched
1.343749e+08 transitions (= visited+matched)
  9740074 atomic steps
hash conflicts:  24722005 (resolved)

Stats on memory usage (in Megabytes):
 3839.701       equivalent memory usage for states (stored*(State-vector + overhead))
 3028.962       actual memory usage for states (compression: 78.89%)
                state-vector as stored = 95 byte + 28 byte overhead
  512.000       memory used for hash table (-w26)
    0.534       memory used for DFS stack (-m10000)
    1.450       memory lost to fragmentation
 3540.046       total actual memory usage



pan: elapsed time 34.7 seconds
pan: rate 1486965.1 states/second
```
