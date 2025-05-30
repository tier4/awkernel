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
Depth=     333 States=    1e+06 Transitions= 1.88e+06 Memory=   187.030	t=     0.49 R=   2e+06
Depth=     333 States=    2e+06 Transitions=  3.5e+06 Memory=   248.651	t=     1.01 R=   2e+06
Depth=     333 States=    3e+06 Transitions= 5.25e+06 Memory=   307.929	t=     1.54 R=   2e+06
Depth=     447 States=    4e+06 Transitions= 7.61e+06 Memory=   367.499	t=     2.12 R=   2e+06
Depth=     447 States=    5e+06 Transitions= 1.02e+07 Memory=   428.046	t=     2.76 R=   2e+06
Depth=     447 States=    6e+06 Transitions= 1.29e+07 Memory=   488.788	t=     3.39 R=   2e+06
Depth=     447 States=    7e+06 Transitions= 1.56e+07 Memory=   547.968	t=      4.1 R=   2e+06
Depth=     447 States=    8e+06 Transitions= 1.83e+07 Memory=   608.808	t=     4.77 R=   2e+06
Depth=     447 States=    9e+06 Transitions=  2.1e+07 Memory=   670.526	t=     5.45 R=   2e+06
Depth=     447 States=    1e+07 Transitions= 2.35e+07 Memory=   730.780	t=     6.11 R=   2e+06
Depth=     447 States=  1.1e+07 Transitions= 2.58e+07 Memory=   795.429	t=     6.79 R=   2e+06
Depth=     447 States=  1.2e+07 Transitions= 2.79e+07 Memory=   849.237	t=     7.43 R=   2e+06
Depth=     447 States=  1.3e+07 Transitions= 3.06e+07 Memory=   909.589	t=     8.13 R=   2e+06
Depth=     447 States=  1.4e+07 Transitions=  3.3e+07 Memory=   969.550	t=     8.78 R=   2e+06
Depth=     447 States=  1.5e+07 Transitions= 3.58e+07 Memory=  1029.511	t=      9.5 R=   2e+06
Depth=     447 States=  1.6e+07 Transitions= 3.86e+07 Memory=  1089.862	t=     10.2 R=   2e+06
Depth=     447 States=  1.7e+07 Transitions= 4.14e+07 Memory=  1150.605	t=       11 R=   2e+06
Depth=     447 States=  1.8e+07 Transitions= 4.44e+07 Memory=  1211.542	t=     11.7 R=   2e+06
Depth=     447 States=  1.9e+07 Transitions= 4.73e+07 Memory=  1271.991	t=     12.5 R=   2e+06
Depth=     447 States=    2e+07 Transitions=    5e+07 Memory=  1332.636	t=     13.2 R=   2e+06
Depth=     447 States=  2.1e+07 Transitions= 5.28e+07 Memory=  1392.401	t=       14 R=   2e+06
Depth=     447 States=  2.2e+07 Transitions= 5.58e+07 Memory=  1458.124	t=     14.8 R=   1e+06
Depth=     447 States=  2.3e+07 Transitions= 5.86e+07 Memory=  1513.690	t=     15.6 R=   1e+06
Depth=     447 States=  2.4e+07 Transitions= 6.15e+07 Memory=  1577.655	t=     16.3 R=   1e+06
Depth=     447 States=  2.5e+07 Transitions=  6.4e+07 Memory=  1644.647	t=     17.1 R=   1e+06
Depth=     447 States=  2.6e+07 Transitions= 6.62e+07 Memory=  1695.331	t=     17.9 R=   1e+06
Depth=     447 States=  2.7e+07 Transitions= 6.88e+07 Memory=  1755.780	t=     18.6 R=   1e+06
Depth=     447 States=  2.8e+07 Transitions= 7.16e+07 Memory=  1816.034	t=     19.4 R=   1e+06
Depth=     447 States=  2.9e+07 Transitions= 7.41e+07 Memory=  1876.776	t=     20.1 R=   1e+06
Depth=     447 States=    3e+07 Transitions= 7.68e+07 Memory=  1937.030	t=     20.9 R=   1e+06
Depth=     447 States=  3.1e+07 Transitions= 7.97e+07 Memory=  1996.991	t=     21.7 R=   1e+06
Depth=     447 States=  3.2e+07 Transitions= 8.26e+07 Memory=  2057.538	t=     22.5 R=   1e+06
Depth=     447 States=  3.3e+07 Transitions= 8.56e+07 Memory=  2117.987	t=     23.3 R=   1e+06
Depth=     447 States=  3.4e+07 Transitions= 8.85e+07 Memory=  2178.632	t=     24.1 R=   1e+06
pan: resizing hashtable to -w26..  done
Depth=     447 States=  3.5e+07 Transitions= 9.14e+07 Memory=  2735.358	t=     25.7 R=   1e+06
Depth=     447 States=  3.6e+07 Transitions= 9.42e+07 Memory=  2796.101	t=     26.4 R=   1e+06
Depth=     447 States=  3.7e+07 Transitions= 9.72e+07 Memory=  2857.038	t=     27.2 R=   1e+06
Depth=     447 States=  3.8e+07 Transitions=    1e+08 Memory=  2917.683	t=     27.9 R=   1e+06
Depth=     447 States=  3.9e+07 Transitions= 1.03e+08 Memory=  2978.230	t=     28.7 R=   1e+06
Depth=     447 States=    4e+07 Transitions= 1.06e+08 Memory=  3038.679	t=     29.4 R=   1e+06
Depth=     447 States=  4.1e+07 Transitions= 1.09e+08 Memory=  3099.226	t=     30.1 R=   1e+06
Depth=     447 States=  4.2e+07 Transitions= 1.12e+08 Memory=  3159.968	t=     30.8 R=   1e+06
Depth=     447 States=  4.3e+07 Transitions= 1.15e+08 Memory=  3220.515	t=     31.5 R=   1e+06
Depth=     447 States=  4.4e+07 Transitions= 1.17e+08 Memory=  3279.694	t=     32.2 R=   1e+06
Depth=     447 States=  4.5e+07 Transitions=  1.2e+08 Memory=  3342.780	t=       33 R=   1e+06
Depth=     447 States=  4.6e+07 Transitions= 1.23e+08 Memory=  3407.624	t=     33.8 R=   1e+06
Depth=     447 States=  4.7e+07 Transitions= 1.26e+08 Memory=  3460.261	t=     34.4 R=   1e+06
Depth=     447 States=  4.8e+07 Transitions= 1.28e+08 Memory=  3521.296	t=     35.1 R=   1e+06
Depth=     447 States=  4.9e+07 Transitions= 1.31e+08 Memory=  3581.647	t=     35.8 R=   1e+06
Depth=     447 States=    5e+07 Transitions= 1.34e+08 Memory=  3641.999	t=     36.5 R=   1e+06
Depth=     447 States=  5.1e+07 Transitions= 1.37e+08 Memory=  3702.937	t=     37.3 R=   1e+06
Depth=     447 States=  5.2e+07 Transitions= 1.39e+08 Memory=  3762.702	t=       38 R=   1e+06
Depth=     447 States=  5.3e+07 Transitions= 1.42e+08 Memory=  3823.347	t=     38.8 R=   1e+06
Depth=     447 States=  5.4e+07 Transitions= 1.45e+08 Memory=  3884.089	t=     39.5 R=   1e+06
Depth=     447 States=  5.5e+07 Transitions= 1.48e+08 Memory=  3944.929	t=     40.3 R=   1e+06
Depth=     447 States=  5.6e+07 Transitions= 1.51e+08 Memory=  4005.183	t=       41 R=   1e+06
Depth=     447 States=  5.7e+07 Transitions= 1.54e+08 Memory=  4066.022	t=     41.8 R=   1e+06
Depth=     447 States=  5.8e+07 Transitions= 1.57e+08 Memory=  4126.765	t=     42.5 R=   1e+06
Depth=     447 States=  5.9e+07 Transitions=  1.6e+08 Memory=  4187.312	t=     43.3 R=   1e+06
Depth=     447 States=    6e+07 Transitions= 1.63e+08 Memory=  4248.054	t=     44.1 R=   1e+06
Depth=     447 States=  6.1e+07 Transitions= 1.66e+08 Memory=  4308.796	t=     44.8 R=   1e+06
Depth=     447 States=  6.2e+07 Transitions= 1.69e+08 Memory=  4369.538	t=     45.5 R=   1e+06
Depth=     447 States=  6.3e+07 Transitions= 1.72e+08 Memory=  4430.183	t=     46.3 R=   1e+06
Depth=     447 States=  6.4e+07 Transitions= 1.74e+08 Memory=  4490.827	t=     47.1 R=   1e+06
Depth=     447 States=  6.5e+07 Transitions= 1.77e+08 Memory=  4551.374	t=     47.9 R=   1e+06
Depth=     447 States=  6.6e+07 Transitions= 1.81e+08 Memory=  4611.823	t=     48.7 R=   1e+06
Depth=     447 States=  6.7e+07 Transitions= 1.84e+08 Memory=  4672.468	t=     49.5 R=   1e+06
Depth=     447 States=  6.8e+07 Transitions= 1.87e+08 Memory=  4733.015	t=     50.3 R=   1e+06
Depth=     447 States=  6.9e+07 Transitions= 1.89e+08 Memory=  4793.562	t=     51.1 R=   1e+06
Depth=     447 States=    7e+07 Transitions= 1.92e+08 Memory=  4853.913	t=     51.8 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
	+ Partial Order Reduction

Full statespace search for:
	never claim         	+ (eventually_execute)
	assertion violations	+ (if within scope of claim)
	acceptance   cycles 	+ (fairness disabled)
	invalid end states	- (disabled by never claim)

State-vector 136 byte, depth reached 447, errors: 0
 35321367 states, stored (7.0627e+07 visited)
1.2348494e+08 states, matched
1.9411191e+08 transitions (= visited+matched)
  3079804 atomic steps
hash conflicts:  36092826 (resolved)

Stats on memory usage (in Megabytes):
 5524.353	equivalent memory usage for states (stored*(State-vector + overhead))
 4380.839	actual memory usage for states (compression: 79.30%)
         	state-vector as stored = 102 byte + 28 byte overhead
  512.000	memory used for hash table (-w26)
    0.534	memory used for DFS stack (-m10000)
    1.479	memory lost to fragmentation
 4891.901	total actual memory usage



pan: elapsed time 52.3 seconds
pan: rate   1350162 states/second
```
