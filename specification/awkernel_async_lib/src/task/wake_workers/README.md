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
Depth=     358 States=    1e+06 Transitions= 1.72e+06 Memory=   186.640 t=     0.44 R=   2e+06
Depth=     358 States=    2e+06 Transitions= 3.32e+06 Memory=   245.917 t=     0.94 R=   2e+06
Depth=     479 States=    3e+06 Transitions= 5.44e+06 Memory=   295.233 t=     1.46 R=   2e+06
Depth=     479 States=    4e+06 Transitions= 7.89e+06 Memory=   351.483 t=     2.04 R=   2e+06
Depth=     479 States=    5e+06 Transitions= 1.04e+07 Memory=   407.147 t=     2.65 R=   2e+06
Depth=     479 States=    6e+06 Transitions= 1.29e+07 Memory=   463.202 t=     3.26 R=   2e+06
Depth=     479 States=    7e+06 Transitions= 1.54e+07 Memory=   519.355 t=     3.88 R=   2e+06
Depth=     479 States=    8e+06 Transitions= 1.75e+07 Memory=   577.460 t=     4.46 R=   2e+06
Depth=     479 States=    9e+06 Transitions= 1.96e+07 Memory=   633.319 t=     5.05 R=   2e+06
Depth=     479 States=    1e+07 Transitions=  2.2e+07 Memory=   689.179 t=     5.66 R=   2e+06
Depth=     479 States=  1.1e+07 Transitions= 2.44e+07 Memory=   745.136 t=     6.26 R=   2e+06
Depth=     479 States=  1.2e+07 Transitions=  2.7e+07 Memory=   801.483 t=     6.91 R=   2e+06
Depth=     479 States=  1.3e+07 Transitions= 2.96e+07 Memory=   858.124 t=     7.55 R=   2e+06
Depth=     479 States=  1.4e+07 Transitions= 3.22e+07 Memory=   914.960 t=     8.22 R=   2e+06
Depth=     479 States=  1.5e+07 Transitions= 3.49e+07 Memory=   970.819 t=     8.88 R=   2e+06
Depth=     479 States=  1.6e+07 Transitions= 3.75e+07 Memory=  1027.362 t=     9.54 R=   2e+06
Depth=     479 States=  1.7e+07 Transitions= 4.01e+07 Memory=  1084.198 t=     10.2 R=   2e+06
Depth=     479 States=  1.8e+07 Transitions= 4.29e+07 Memory=  1144.843 t=       11 R=   2e+06
Depth=     479 States=  1.9e+07 Transitions= 4.52e+07 Memory=  1201.972 t=     11.6 R=   2e+06
Depth=     479 States=    2e+07 Transitions= 4.74e+07 Memory=  1255.097 t=     12.3 R=   2e+06
Depth=     479 States=  2.1e+07 Transitions= 4.99e+07 Memory=  1311.542 t=       13 R=   2e+06
Depth=     479 States=  2.2e+07 Transitions= 5.24e+07 Memory=  1368.085 t=     13.7 R=   2e+06
Depth=     479 States=  2.3e+07 Transitions= 5.47e+07 Memory=  1424.433 t=     14.3 R=   2e+06
Depth=     479 States=  2.4e+07 Transitions= 5.74e+07 Memory=  1480.390 t=       15 R=   2e+06
Depth=     479 States=  2.5e+07 Transitions=    6e+07 Memory=  1537.128 t=     15.7 R=   2e+06
Depth=     479 States=  2.6e+07 Transitions= 6.27e+07 Memory=  1593.573 t=     16.4 R=   2e+06
Depth=     479 States=  2.7e+07 Transitions= 6.55e+07 Memory=  1650.507 t=     17.2 R=   2e+06
Depth=     479 States=  2.8e+07 Transitions= 6.82e+07 Memory=  1707.147 t=     17.9 R=   2e+06
Depth=     479 States=  2.9e+07 Transitions= 7.08e+07 Memory=  1764.179 t=     18.6 R=   2e+06
Depth=     479 States=    3e+07 Transitions= 7.34e+07 Memory=  1820.917 t=     19.4 R=   2e+06
Depth=     479 States=  3.1e+07 Transitions= 7.62e+07 Memory=  1877.460 t=     20.1 R=   2e+06
Depth=     479 States=  3.2e+07 Transitions= 7.88e+07 Memory=  1934.198 t=     20.8 R=   2e+06
Depth=     479 States=  3.3e+07 Transitions= 8.15e+07 Memory=  1991.034 t=     21.6 R=   2e+06
Depth=     479 States=  3.4e+07 Transitions= 8.41e+07 Memory=  2047.772 t=     22.3 R=   2e+06
pan: resizing hashtable to -w26..  done
Depth=     479 States=  3.5e+07 Transitions= 8.69e+07 Memory=  2602.839 t=     23.9 R=   1e+06
Depth=     479 States=  3.6e+07 Transitions= 8.94e+07 Memory=  2656.062 t=     24.5 R=   1e+06
Depth=     479 States=  3.7e+07 Transitions= 9.19e+07 Memory=  2713.190 t=     25.2 R=   1e+06
Depth=     479 States=  3.8e+07 Transitions= 9.44e+07 Memory=  2769.147 t=     25.8 R=   1e+06
Depth=     479 States=  3.9e+07 Transitions= 9.69e+07 Memory=  2826.081 t=     26.4 R=   1e+06
Depth=     479 States=    4e+07 Transitions= 9.96e+07 Memory=  2883.503 t=     27.1 R=   1e+06
Depth=     479 States=  4.1e+07 Transitions= 1.02e+08 Memory=  2938.581 t=     27.7 R=   1e+06
Depth=     479 States=  4.2e+07 Transitions= 1.05e+08 Memory=  2995.319 t=     28.4 R=   1e+06
Depth=     479 States=  4.3e+07 Transitions= 1.08e+08 Memory=  3052.253 t=     29.1 R=   1e+06
Depth=     479 States=  4.4e+07 Transitions=  1.1e+08 Memory=  3109.382 t=     29.8 R=   1e+06
Depth=     479 States=  4.5e+07 Transitions= 1.13e+08 Memory=  3165.534 t=     30.4 R=   1e+06
Depth=     479 States=  4.6e+07 Transitions= 1.16e+08 Memory=  3222.370 t=     31.1 R=   1e+06
Depth=     479 States=  4.7e+07 Transitions= 1.19e+08 Memory=  3279.401 t=     31.8 R=   1e+06
Depth=     479 States=  4.8e+07 Transitions= 1.21e+08 Memory=  3336.140 t=     32.5 R=   1e+06
Depth=     479 States=  4.9e+07 Transitions= 1.24e+08 Memory=  3393.073 t=     33.2 R=   1e+06
Depth=     479 States=    5e+07 Transitions= 1.27e+08 Memory=  3449.714 t=     33.8 R=   1e+06
Depth=     479 States=  5.1e+07 Transitions= 1.29e+08 Memory=  3506.452 t=     34.5 R=   1e+06
Depth=     479 States=  5.2e+07 Transitions= 1.32e+08 Memory=  3562.995 t=     35.2 R=   1e+06
Depth=     479 States=  5.3e+07 Transitions= 1.35e+08 Memory=  3619.831 t=     35.9 R=   1e+06
Depth=     479 States=  5.4e+07 Transitions= 1.38e+08 Memory=  3676.472 t=     36.6 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (eventually_execute)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 128 byte, depth reached 479, errors: 0
 27335088 states, stored (5.46646e+07 visited)
 84606226 states, matched
1.3927078e+08 transitions (= visited+matched)
  4432736 atomic steps
hash conflicts:  25312489 (resolved)

Stats on memory usage (in Megabytes):
 4066.728       equivalent memory usage for states (stored*(State-vector + overhead))
 3203.248       actual memory usage for states (compression: 78.77%)
                state-vector as stored = 95 byte + 28 byte overhead
  512.000       memory used for hash table (-w26)
    0.534       memory used for DFS stack (-m10000)
    1.525       memory lost to fragmentation
 3714.265       total actual memory usage



pan: elapsed time 37 seconds
pan: rate 1475426.5 states/second
```
