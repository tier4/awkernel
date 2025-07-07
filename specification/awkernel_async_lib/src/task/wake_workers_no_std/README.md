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

## Result

```
$ make run
spin -a wake_workers.pml
ltl eventually_execute: <> ([] ((run_queue==0)))
gcc -O3 -DCOLLAPSE -o pan pan.c
rm -f *.trail
./pan -a -n
Depth=     661 States=    1e+06 Transitions= 1.63e+06 Memory=   169.647	t=     0.74 R=   1e+06
Depth=     787 States=    2e+06 Transitions= 3.35e+06 Memory=   195.233	t=     1.51 R=   1e+06
Depth=     787 States=    3e+06 Transitions= 5.09e+06 Memory=   248.944	t=     2.34 R=   1e+06
Depth=     787 States=    4e+06 Transitions= 6.87e+06 Memory=   251.874	t=     3.14 R=   1e+06
Depth=     787 States=    5e+06 Transitions=  8.6e+06 Memory=   270.917	t=     3.94 R=   1e+06
Depth=     787 States=    6e+06 Transitions= 1.04e+07 Memory=   305.097	t=     4.77 R=   1e+06
Depth=     787 States=    7e+06 Transitions= 1.21e+07 Memory=   322.187	t=     5.59 R=   1e+06
Depth=     787 States=    8e+06 Transitions= 1.39e+07 Memory=   351.581	t=     6.44 R=   1e+06
Depth=     787 States=    9e+06 Transitions= 1.57e+07 Memory=   388.300	t=     7.29 R=   1e+06
Depth=     787 States=    1e+07 Transitions= 1.75e+07 Memory=   400.409	t=     8.11 R=   1e+06
Depth=     787 States=  1.1e+07 Transitions= 1.93e+07 Memory=   424.726	t=     8.96 R=   1e+06
Depth=     787 States=  1.2e+07 Transitions= 2.11e+07 Memory=   451.776	t=     9.79 R=   1e+06
Depth=     787 States=  1.3e+07 Transitions= 2.29e+07 Memory=   478.046	t=     10.7 R=   1e+06
Depth=     787 States=  1.4e+07 Transitions= 2.49e+07 Memory=   504.999	t=     11.5 R=   1e+06
Depth=     787 States=  1.5e+07 Transitions= 2.68e+07 Memory=   532.050	t=     12.4 R=   1e+06
Depth=     817 States=  1.6e+07 Transitions= 2.86e+07 Memory=   558.417	t=     13.3 R=   1e+06
Depth=     817 States=  1.7e+07 Transitions= 3.05e+07 Memory=   585.468	t=     14.1 R=   1e+06
Depth=     817 States=  1.8e+07 Transitions= 3.24e+07 Memory=   612.030	t=       15 R=   1e+06
Depth=     817 States=  1.9e+07 Transitions= 3.41e+07 Memory=   655.292	t=     15.9 R=   1e+06
Depth=     847 States=    2e+07 Transitions= 3.59e+07 Memory=   686.933	t=     16.8 R=   1e+06
Depth=     847 States=  2.1e+07 Transitions= 3.77e+07 Memory=   713.202	t=     17.7 R=   1e+06
Depth=     847 States=  2.2e+07 Transitions= 3.95e+07 Memory=   744.452	t=     18.7 R=   1e+06
Depth=     847 States=  2.3e+07 Transitions= 4.13e+07 Memory=   762.909	t=     19.6 R=   1e+06
Depth=     857 States=  2.4e+07 Transitions= 4.33e+07 Memory=   791.425	t=     20.6 R=   1e+06
Depth=     917 States=  2.5e+07 Transitions= 4.52e+07 Memory=   816.913	t=     21.5 R=   1e+06
Depth=     917 States=  2.6e+07 Transitions= 4.71e+07 Memory=   843.573	t=     22.4 R=   1e+06
Depth=     917 States=  2.7e+07 Transitions= 4.89e+07 Memory=   869.940	t=     23.4 R=   1e+06
Depth=     917 States=  2.8e+07 Transitions= 5.11e+07 Memory=   896.894	t=     24.4 R=   1e+06
Depth=     917 States=  2.9e+07 Transitions= 5.33e+07 Memory=   923.847	t=     25.4 R=   1e+06
Depth=     917 States=    3e+07 Transitions= 5.51e+07 Memory=   933.222	t=     26.3 R=   1e+06
Depth=     917 States=  3.1e+07 Transitions= 5.69e+07 Memory=   978.144	t=     27.3 R=   1e+06
Depth=     917 States=  3.2e+07 Transitions= 5.87e+07 Memory=   987.714	t=     28.2 R=   1e+06
Depth=     917 States=  3.3e+07 Transitions= 6.05e+07 Memory=  1017.011	t=     29.2 R=   1e+06
Depth=     917 States=  3.4e+07 Transitions= 6.23e+07 Memory=  1040.741	t=     30.2 R=   1e+06
pan: resizing hashtable to -w26..  done
Depth=     917 States=  3.5e+07 Transitions= 6.41e+07 Memory=  1563.874	t=       32 R=   1e+06
Depth=     917 States=  3.6e+07 Transitions=  6.6e+07 Memory=  1590.730	t=     32.9 R=   1e+06
Depth=     959 States=  3.7e+07 Transitions= 6.79e+07 Memory=  1617.292	t=     33.8 R=   1e+06
Depth=     959 States=  3.8e+07 Transitions= 6.97e+07 Memory=  1644.245	t=     34.7 R=   1e+06
Depth=     959 States=  3.9e+07 Transitions= 7.16e+07 Memory=  1670.710	t=     35.5 R=   1e+06
Depth=     959 States=    4e+07 Transitions= 7.36e+07 Memory=  1697.663	t=     36.4 R=   1e+06
Depth=     959 States=  4.1e+07 Transitions= 7.57e+07 Memory=  1724.421	t=     37.4 R=   1e+06
Depth=     959 States=  4.2e+07 Transitions= 7.79e+07 Memory=  1752.448	t=     38.3 R=   1e+06
Depth=     959 States=  4.3e+07 Transitions= 8.01e+07 Memory=  1780.671	t=     39.3 R=   1e+06
Depth=     959 States=  4.4e+07 Transitions= 8.21e+07 Memory=  1809.870	t=     40.2 R=   1e+06
Depth=     959 States=  4.5e+07 Transitions= 8.39e+07 Memory=  1859.870	t=     41.1 R=   1e+06
Depth=     959 States=  4.6e+07 Transitions= 8.61e+07 Memory=  1897.956	t=     42.1 R=   1e+06
Depth=     959 States=  4.7e+07 Transitions= 8.82e+07 Memory=  1907.917	t=     43.1 R=   1e+06
Depth=     959 States=  4.8e+07 Transitions= 9.01e+07 Memory=  1918.073	t=       44 R=   1e+06
Depth=     959 States=  4.9e+07 Transitions= 9.21e+07 Memory=  1962.409	t=       45 R=   1e+06
Depth=     959 States=    5e+07 Transitions= 9.43e+07 Memory=  1983.698	t=       46 R=   1e+06
Depth=     959 States=  5.1e+07 Transitions= 9.61e+07 Memory=  1993.269	t=     46.8 R=   1e+06
Depth=     959 States=  5.2e+07 Transitions=  9.8e+07 Memory=  2019.440	t=     47.8 R=   1e+06
Depth=     959 States=  5.3e+07 Transitions=    1e+08 Memory=  2045.808	t=     48.7 R=   1e+06
Depth=     959 States=  5.4e+07 Transitions= 1.02e+08 Memory=  2072.468	t=     49.7 R=   1e+06
Depth=     959 States=  5.5e+07 Transitions= 1.04e+08 Memory=  2099.323	t=     50.6 R=   1e+06
Depth=     959 States=  5.6e+07 Transitions= 1.06e+08 Memory=  2126.667	t=     51.5 R=   1e+06
Depth=     959 States=  5.7e+07 Transitions= 1.09e+08 Memory=  2153.425	t=     52.5 R=   1e+06
Depth=     959 States=  5.8e+07 Transitions= 1.11e+08 Memory=  2180.671	t=     53.5 R=   1e+06
Depth=     959 States=  5.9e+07 Transitions= 1.13e+08 Memory=  2206.550	t=     54.5 R=   1e+06
Depth=     959 States=    6e+07 Transitions= 1.16e+08 Memory=  2233.796	t=     55.6 R=   1e+06
Depth=     959 States=  6.1e+07 Transitions= 1.18e+08 Memory=  2262.312	t=     56.6 R=   1e+06
Depth=     959 States=  6.2e+07 Transitions=  1.2e+08 Memory=  2286.726	t=     57.7 R=   1e+06
Depth=     959 States=  6.3e+07 Transitions= 1.23e+08 Memory=  2313.679	t=     58.7 R=   1e+06
Depth=     959 States=  6.4e+07 Transitions= 1.25e+08 Memory=  2340.241	t=     59.8 R=   1e+06
Depth=     959 States=  6.5e+07 Transitions= 1.27e+08 Memory=  2367.097	t=     60.8 R=   1e+06
Depth=     959 States=  6.6e+07 Transitions= 1.29e+08 Memory=  2393.855	t=     61.8 R=   1e+06
Depth=     959 States=  6.7e+07 Transitions= 1.31e+08 Memory=  2420.515	t=     62.8 R=   1e+06
Depth=     959 States=  6.8e+07 Transitions= 1.34e+08 Memory=  2447.956	t=     63.9 R=   1e+06
Depth=     959 States=  6.9e+07 Transitions= 1.36e+08 Memory=  2473.151	t=     64.8 R=   1e+06
Depth=     959 States=    7e+07 Transitions= 1.38e+08 Memory=  2501.081	t=     65.8 R=   1e+06
Depth=     959 States=  7.1e+07 Transitions=  1.4e+08 Memory=  2526.765	t=     66.8 R=   1e+06
Depth=     959 States=  7.2e+07 Transitions= 1.42e+08 Memory=  2553.522	t=     67.8 R=   1e+06
Depth=     959 States=  7.3e+07 Transitions= 1.45e+08 Memory=  2583.112	t=     68.9 R=   1e+06
Depth=     959 States=  7.4e+07 Transitions= 1.47e+08 Memory=  2609.968	t=     69.8 R=   1e+06
Depth=    1049 States=  7.5e+07 Transitions= 1.49e+08 Memory=  2636.823	t=     70.8 R=   1e+06
Depth=    1049 States=  7.6e+07 Transitions= 1.51e+08 Memory=  2663.874	t=     71.9 R=   1e+06
Depth=    1049 States=  7.7e+07 Transitions= 1.54e+08 Memory=  2690.534	t=       73 R=   1e+06
Depth=    1049 States=  7.8e+07 Transitions= 1.56e+08 Memory=  2714.265	t=     74.1 R=   1e+06
Depth=    1049 States=  7.9e+07 Transitions= 1.58e+08 Memory=  2742.194	t=     75.2 R=   1e+06
Depth=    1049 States=    8e+07 Transitions= 1.61e+08 Memory=  2768.269	t=     76.3 R=   1e+06
Depth=    1049 States=  8.1e+07 Transitions= 1.63e+08 Memory=  2795.124	t=     77.3 R=   1e+06
Depth=    1049 States=  8.2e+07 Transitions= 1.65e+08 Memory=  2821.491	t=     78.3 R=   1e+06
Depth=    1049 States=  8.3e+07 Transitions= 1.67e+08 Memory=  2847.956	t=     79.4 R=   1e+06
Depth=    1049 States=  8.4e+07 Transitions= 1.69e+08 Memory=  2874.714	t=     80.4 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
	+ Partial Order Reduction
	+ Compression

Full statespace search for:
	never claim         	+ (eventually_execute)
	assertion violations	+ (if within scope of claim)
	acceptance   cycles 	+ (fairness disabled)
	invalid end states	- (disabled by never claim)

State-vector 96 byte, depth reached 1049, errors: 0
 42082482 states, stored (8.4165e+07 visited)
 85566862 states, matched
1.6973182e+08 transitions (= visited+matched)
        0 atomic steps
hash conflicts:  35600021 (resolved)

Stats on memory usage (in Megabytes):
 5297.554	equivalent memory usage for states (stored*(State-vector + overhead))
 2367.205	actual memory usage for states (compression: 44.68%)
         	state-vector as stored = 23 byte + 36 byte overhead
  512.000	memory used for hash table (-w26)
    0.534	memory used for DFS stack (-m10000)
 2879.011	total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:115315 2:98 3:340 4:3 5:44 6:2 ]

pan: elapsed time 80.5 seconds
pan: rate 1044878.5 states/second
```
