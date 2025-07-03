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
Depth=     661 States=    1e+06 Transitions= 1.63e+06 Memory=   170.136	t=     0.71 R=   1e+06
Depth=     789 States=    2e+06 Transitions= 3.35e+06 Memory=   194.745	t=     1.45 R=   1e+06
Depth=     789 States=    3e+06 Transitions=  5.1e+06 Memory=   248.456	t=     2.24 R=   1e+06
Depth=     789 States=    4e+06 Transitions= 6.88e+06 Memory=   254.022	t=     3.01 R=   1e+06
Depth=     789 States=    5e+06 Transitions= 8.61e+06 Memory=   268.769	t=     3.77 R=   1e+06
Depth=     789 States=    6e+06 Transitions= 1.04e+07 Memory=   302.460	t=     4.56 R=   1e+06
Depth=     789 States=    7e+06 Transitions= 1.21e+07 Memory=   325.605	t=     5.34 R=   1e+06
Depth=     789 States=    8e+06 Transitions=  1.4e+07 Memory=   354.901	t=     6.15 R=   1e+06
Depth=     789 States=    9e+06 Transitions= 1.57e+07 Memory=   384.296	t=     6.95 R=   1e+06
Depth=     789 States=    1e+07 Transitions= 1.75e+07 Memory=   397.772	t=     7.75 R=   1e+06
Depth=     789 States=  1.1e+07 Transitions= 1.93e+07 Memory=   423.651	t=     8.56 R=   1e+06
Depth=     789 States=  1.2e+07 Transitions= 2.11e+07 Memory=   451.288	t=     9.34 R=   1e+06
Depth=     789 States=  1.3e+07 Transitions= 2.29e+07 Memory=   478.144	t=     10.2 R=   1e+06
Depth=     789 States=  1.4e+07 Transitions= 2.49e+07 Memory=   504.804	t=       11 R=   1e+06
Depth=     789 States=  1.5e+07 Transitions= 2.68e+07 Memory=   531.562	t=     11.8 R=   1e+06
Depth=     819 States=  1.6e+07 Transitions= 2.87e+07 Memory=   558.515	t=     12.7 R=   1e+06
Depth=     819 States=  1.7e+07 Transitions= 3.05e+07 Memory=   585.565	t=     13.5 R=   1e+06
Depth=     819 States=  1.8e+07 Transitions= 3.24e+07 Memory=   611.933	t=     14.3 R=   1e+06
Depth=     819 States=  1.9e+07 Transitions= 3.43e+07 Memory=   646.112	t=     15.1 R=   1e+06
Depth=     819 States=    2e+07 Transitions=  3.6e+07 Memory=   682.343	t=       16 R=   1e+06
Depth=     847 States=  2.1e+07 Transitions= 3.78e+07 Memory=   711.151	t=     16.9 R=   1e+06
Depth=     847 States=  2.2e+07 Transitions= 3.96e+07 Memory=   736.151	t=     17.8 R=   1e+06
Depth=     847 States=  2.3e+07 Transitions= 4.14e+07 Memory=   763.007	t=     18.6 R=   1e+06
Depth=     857 States=  2.4e+07 Transitions= 4.33e+07 Memory=   790.058	t=     19.5 R=   1e+06
Depth=     857 States=  2.5e+07 Transitions= 4.52e+07 Memory=   816.522	t=     20.4 R=   1e+06
Depth=     919 States=  2.6e+07 Transitions= 4.71e+07 Memory=   843.378	t=     21.3 R=   1e+06
Depth=     919 States=  2.7e+07 Transitions=  4.9e+07 Memory=   870.429	t=     22.2 R=   1e+06
Depth=     919 States=  2.8e+07 Transitions=  5.1e+07 Memory=   896.894	t=     23.1 R=   1e+06
Depth=     919 States=  2.9e+07 Transitions= 5.32e+07 Memory=   923.847	t=     24.1 R=   1e+06
Depth=     919 States=    3e+07 Transitions= 5.53e+07 Memory=   939.081	t=       25 R=   1e+06
Depth=     919 States=  3.1e+07 Transitions= 5.71e+07 Memory=   964.472	t=     25.9 R=   1e+06
Depth=     919 States=  3.2e+07 Transitions= 5.88e+07 Memory=   998.944	t=     26.8 R=   1e+06
Depth=     919 States=  3.3e+07 Transitions= 6.06e+07 Memory=  1015.058	t=     27.8 R=   1e+06
Depth=     919 States=  3.4e+07 Transitions= 6.24e+07 Memory=  1048.651	t=     28.7 R=   1e+06
pan: resizing hashtable to -w26..  done
Depth=     919 States=  3.5e+07 Transitions= 6.43e+07 Memory=  1565.144	t=     30.5 R=   1e+06
Depth=     919 States=  3.6e+07 Transitions= 6.61e+07 Memory=  1592.878	t=     31.3 R=   1e+06
Depth=     963 States=  3.7e+07 Transitions=  6.8e+07 Memory=  1617.097	t=     32.2 R=   1e+06
Depth=     963 States=  3.8e+07 Transitions= 6.99e+07 Memory=  1644.147	t=       33 R=   1e+06
Depth=     963 States=  3.9e+07 Transitions= 7.17e+07 Memory=  1670.612	t=     33.9 R=   1e+06
Depth=     963 States=    4e+07 Transitions= 7.37e+07 Memory=  1697.370	t=     34.7 R=   1e+06
Depth=     963 States=  4.1e+07 Transitions= 7.57e+07 Memory=  1724.128	t=     35.6 R=   1e+06
Depth=     963 States=  4.2e+07 Transitions= 7.78e+07 Memory=  1751.081	t=     36.5 R=   1e+06
Depth=     963 States=  4.3e+07 Transitions=    8e+07 Memory=  1778.425	t=     37.5 R=   1e+06
Depth=     963 States=  4.4e+07 Transitions= 8.22e+07 Memory=  1809.089	t=     38.4 R=   1e+06
Depth=     963 States=  4.5e+07 Transitions= 8.41e+07 Memory=  1842.878	t=     39.3 R=   1e+06
Depth=     963 States=  4.6e+07 Transitions= 8.59e+07 Memory=  1896.687	t=     40.1 R=   1e+06
Depth=     963 States=  4.7e+07 Transitions= 8.84e+07 Memory=  1925.593	t=     41.2 R=   1e+06
Depth=     963 States=  4.8e+07 Transitions= 9.02e+07 Memory=  1925.886	t=       42 R=   1e+06
Depth=     963 States=  4.9e+07 Transitions= 9.21e+07 Memory=  1953.327	t=     42.9 R=   1e+06
Depth=     963 States=    5e+07 Transitions= 9.43e+07 Memory=  1989.851	t=     43.9 R=   1e+06
Depth=     963 States=  5.1e+07 Transitions= 9.63e+07 Memory=  2002.839	t=     44.8 R=   1e+06
Depth=     963 States=  5.2e+07 Transitions= 9.81e+07 Memory=  2019.050	t=     45.7 R=   1e+06
Depth=     963 States=  5.3e+07 Transitions=    1e+08 Memory=  2045.710	t=     46.6 R=   1e+06
Depth=     963 States=  5.4e+07 Transitions= 1.02e+08 Memory=  2072.468	t=     47.5 R=   1e+06
Depth=     963 States=  5.5e+07 Transitions= 1.04e+08 Memory=  2099.226	t=     48.4 R=   1e+06
Depth=     963 States=  5.6e+07 Transitions= 1.07e+08 Memory=  2126.765	t=     49.4 R=   1e+06
Depth=     963 States=  5.7e+07 Transitions= 1.09e+08 Memory=  2153.327	t=     50.2 R=   1e+06
Depth=     963 States=  5.8e+07 Transitions= 1.11e+08 Memory=  2180.183	t=     51.1 R=   1e+06
Depth=     963 States=  5.9e+07 Transitions= 1.13e+08 Memory=  2208.308	t=     52.1 R=   1e+06
Depth=     963 States=    6e+07 Transitions= 1.15e+08 Memory=  2233.601	t=     53.1 R=   1e+06
Depth=     963 States=  6.1e+07 Transitions= 1.18e+08 Memory=  2260.651	t=     54.1 R=   1e+06
Depth=     963 States=  6.2e+07 Transitions=  1.2e+08 Memory=  2286.628	t=     55.1 R=   1e+06
Depth=     963 States=  6.3e+07 Transitions= 1.22e+08 Memory=  2313.581	t=     56.1 R=   1e+06
Depth=     963 States=  6.4e+07 Transitions= 1.25e+08 Memory=  2341.120	t=     57.2 R=   1e+06
Depth=     963 States=  6.5e+07 Transitions= 1.27e+08 Memory=  2366.804	t=     58.2 R=   1e+06
Depth=     963 States=  6.6e+07 Transitions= 1.29e+08 Memory=  2393.952	t=     59.1 R=   1e+06
Depth=     963 States=  6.7e+07 Transitions= 1.31e+08 Memory=  2421.198	t=     60.1 R=   1e+06
Depth=     963 States=  6.8e+07 Transitions= 1.34e+08 Memory=  2447.077	t=     61.1 R=   1e+06
Depth=     963 States=  6.9e+07 Transitions= 1.36e+08 Memory=  2474.030	t=     62.1 R=   1e+06
Depth=     963 States=    7e+07 Transitions= 1.38e+08 Memory=  2499.812	t=     63.1 R=   1e+06
Depth=     963 States=  7.1e+07 Transitions=  1.4e+08 Memory=  2527.741	t=       64 R=   1e+06
Depth=     963 States=  7.2e+07 Transitions= 1.42e+08 Memory=  2553.425	t=       65 R=   1e+06
Depth=     963 States=  7.3e+07 Transitions= 1.45e+08 Memory=  2581.550	t=       66 R=   1e+06
Depth=     963 States=  7.4e+07 Transitions= 1.47e+08 Memory=  2609.675	t=     67.1 R=   1e+06
Depth=     963 States=  7.5e+07 Transitions= 1.49e+08 Memory=  2636.726	t=       68 R=   1e+06
Depth=    1047 States=  7.6e+07 Transitions= 1.51e+08 Memory=  2663.386	t=       69 R=   1e+06
Depth=    1047 States=  7.7e+07 Transitions= 1.54e+08 Memory=  2690.437	t=       70 R=   1e+06
Depth=    1047 States=  7.8e+07 Transitions= 1.56e+08 Memory=  2717.487	t=       71 R=   1e+06
Depth=    1047 States=  7.9e+07 Transitions= 1.58e+08 Memory=  2740.730	t=     72.1 R=   1e+06
Depth=    1047 States=    8e+07 Transitions=  1.6e+08 Memory=  2768.952	t=     73.1 R=   1e+06
Depth=    1047 States=  8.1e+07 Transitions= 1.63e+08 Memory=  2794.929	t=     74.1 R=   1e+06
Depth=    1047 States=  8.2e+07 Transitions= 1.65e+08 Memory=  2821.003	t=     75.1 R=   1e+06
Depth=    1047 States=  8.3e+07 Transitions= 1.67e+08 Memory=  2848.054	t=     76.1 R=   1e+06
Depth=    1047 States=  8.4e+07 Transitions= 1.69e+08 Memory=  2874.519	t=     77.1 R=   1e+06
Depth=    1047 States=  8.5e+07 Transitions= 1.72e+08 Memory=  2901.569	t=     78.1 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
	+ Partial Order Reduction
	+ Compression

Full statespace search for:
	never claim         	+ (eventually_execute)
	assertion violations	+ (if within scope of claim)
	acceptance   cycles 	+ (fairness disabled)
	invalid end states	- (disabled by never claim)

State-vector 96 byte, depth reached 1047, errors: 0
 42698624 states, stored (8.53972e+07 visited)
 87127237 states, matched
1.7252448e+08 transitions (= visited+matched)
        0 atomic steps
hash conflicts:  35657494 (resolved)

Stats on memory usage (in Megabytes):
 5375.117	equivalent memory usage for states (stored*(State-vector + overhead))
 2400.019	actual memory usage for states (compression: 44.65%)
         	state-vector as stored = 23 byte + 36 byte overhead
  512.000	memory used for hash table (-w26)
    0.534	memory used for DFS stack (-m10000)
 2911.823	total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:112777 2:98 3:341 4:3 5:44 6:2 ]

pan: elapsed time 78.5 seconds
pan: rate 1087724.4 states/second
```
