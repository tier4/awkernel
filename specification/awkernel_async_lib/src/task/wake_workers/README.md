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
Depth=     371 States=    1e+06 Transitions= 1.76e+06 Memory=   185.858	t=     0.48 R=   2e+06
Depth=     371 States=    2e+06 Transitions= 3.33e+06 Memory=   248.847	t=     0.97 R=   2e+06
Depth=     371 States=    3e+06 Transitions= 4.91e+06 Memory=   309.980	t=     1.49 R=   2e+06
Depth=     371 States=    4e+06 Transitions= 6.97e+06 Memory=   366.034	t=     2.04 R=   2e+06
Depth=     495 States=    5e+06 Transitions=  9.2e+06 Memory=   425.605	t=     2.61 R=   2e+06
Depth=     495 States=    6e+06 Transitions= 1.16e+07 Memory=   486.347	t=     3.21 R=   2e+06
Depth=     495 States=    7e+06 Transitions= 1.41e+07 Memory=   546.796	t=     3.82 R=   2e+06
Depth=     495 States=    8e+06 Transitions= 1.66e+07 Memory=   604.608	t=     4.48 R=   2e+06
Depth=     495 States=    9e+06 Transitions= 1.92e+07 Memory=   669.452	t=     5.15 R=   2e+06
Depth=     495 States=    1e+07 Transitions= 2.17e+07 Memory=   725.214	t=      5.8 R=   2e+06
Depth=     495 States=  1.1e+07 Transitions= 2.42e+07 Memory=   785.175	t=     6.45 R=   2e+06
Depth=     495 States=  1.2e+07 Transitions= 2.63e+07 Memory=   846.894	t=     7.06 R=   2e+06
Depth=     495 States=  1.3e+07 Transitions= 2.84e+07 Memory=   907.050	t=     7.69 R=   2e+06
Depth=     495 States=  1.4e+07 Transitions= 3.04e+07 Memory=   971.991	t=     8.32 R=   2e+06
Depth=     495 States=  1.5e+07 Transitions= 3.26e+07 Memory=  1026.972	t=     8.93 R=   2e+06
Depth=     495 States=  1.6e+07 Transitions= 3.52e+07 Memory=  1086.347	t=     9.62 R=   2e+06
Depth=     495 States=  1.7e+07 Transitions= 3.74e+07 Memory=  1146.698	t=     10.2 R=   2e+06
Depth=     495 States=  1.8e+07 Transitions= 3.99e+07 Memory=  1206.366	t=     10.9 R=   2e+06
Depth=     495 States=  1.9e+07 Transitions= 4.26e+07 Memory=  1266.620	t=     11.6 R=   2e+06
Depth=     495 States=    2e+07 Transitions= 4.51e+07 Memory=  1327.167	t=     12.3 R=   2e+06
Depth=     495 States=  2.1e+07 Transitions= 4.77e+07 Memory=  1388.105	t=       13 R=   2e+06
Depth=     495 States=  2.2e+07 Transitions= 5.03e+07 Memory=  1448.847	t=     13.7 R=   2e+06
Depth=     495 States=  2.3e+07 Transitions=  5.3e+07 Memory=  1509.198	t=     14.5 R=   2e+06
Depth=     495 States=  2.4e+07 Transitions= 5.55e+07 Memory=  1567.792	t=     15.2 R=   2e+06
Depth=     495 States=  2.5e+07 Transitions= 5.81e+07 Memory=  1627.948	t=     15.9 R=   2e+06
Depth=     495 States=  2.6e+07 Transitions= 6.08e+07 Memory=  1690.155	t=     16.6 R=   2e+06
Depth=     495 States=  2.7e+07 Transitions= 6.35e+07 Memory=  1753.046	t=     17.4 R=   2e+06
Depth=     495 States=  2.8e+07 Transitions= 6.62e+07 Memory=  1811.054	t=     18.2 R=   2e+06
Depth=     495 States=  2.9e+07 Transitions= 6.89e+07 Memory=  1876.776	t=       19 R=   2e+06
Depth=     495 States=    3e+07 Transitions= 7.11e+07 Memory=  1932.245	t=     19.7 R=   2e+06
Depth=     495 States=  3.1e+07 Transitions= 7.33e+07 Memory=  1992.792	t=     20.4 R=   2e+06
Depth=     495 States=  3.2e+07 Transitions= 7.54e+07 Memory=  2052.948	t=     21.1 R=   2e+06
Depth=     495 States=  3.3e+07 Transitions= 7.78e+07 Memory=  2112.812	t=     21.8 R=   2e+06
Depth=     495 States=  3.4e+07 Transitions= 8.05e+07 Memory=  2173.261	t=     22.6 R=   2e+06
pan: resizing hashtable to -w26..  done
Depth=     495 States=  3.5e+07 Transitions= 8.27e+07 Memory=  2729.694	t=     24.1 R=   1e+06
Depth=     495 States=  3.6e+07 Transitions= 8.51e+07 Memory=  2789.851	t=     24.8 R=   1e+06
Depth=     495 States=  3.7e+07 Transitions= 8.77e+07 Memory=  2850.105	t=     25.4 R=   1e+06
Depth=     495 States=  3.8e+07 Transitions= 9.04e+07 Memory=  2910.163	t=     26.1 R=   1e+06
Depth=     495 States=  3.9e+07 Transitions=  9.3e+07 Memory=  2970.905	t=     26.8 R=   1e+06
Depth=     495 States=    4e+07 Transitions= 9.57e+07 Memory=  3030.964	t=     27.5 R=   1e+06
Depth=     495 States=  4.1e+07 Transitions= 9.85e+07 Memory=  3091.608	t=     28.2 R=   1e+06
Depth=     495 States=  4.2e+07 Transitions= 1.01e+08 Memory=  3152.155	t=     28.9 R=   1e+06
Depth=     495 States=  4.3e+07 Transitions= 1.04e+08 Memory=  3212.702	t=     29.6 R=   1e+06
Depth=     495 States=  4.4e+07 Transitions= 1.06e+08 Memory=  3273.347	t=     30.2 R=   1e+06
Depth=     495 States=  4.5e+07 Transitions= 1.09e+08 Memory=  3334.284	t=     30.9 R=   1e+06
Depth=     495 States=  4.6e+07 Transitions= 1.12e+08 Memory=  3395.026	t=     31.6 R=   1e+06
Depth=     495 States=  4.7e+07 Transitions= 1.14e+08 Memory=  3455.573	t=     32.3 R=   1e+06
Depth=     495 States=  4.8e+07 Transitions= 1.17e+08 Memory=  3515.925	t=       33 R=   1e+06
Depth=     495 States=  4.9e+07 Transitions=  1.2e+08 Memory=  3576.276	t=     33.7 R=   1e+06
Depth=     495 States=    5e+07 Transitions= 1.22e+08 Memory=  3637.019	t=     34.4 R=   1e+06
Depth=     495 States=  5.1e+07 Transitions= 1.25e+08 Memory=  3697.272	t=     35.1 R=   1e+06
Depth=     495 States=  5.2e+07 Transitions= 1.28e+08 Memory=  3758.015	t=     35.8 R=   1e+06
Depth=     495 States=  5.3e+07 Transitions=  1.3e+08 Memory=  3818.562	t=     36.5 R=   1e+06
Depth=     495 States=  5.4e+07 Transitions= 1.33e+08 Memory=  3879.401	t=     37.2 R=   1e+06
Depth=     495 States=  5.5e+07 Transitions= 1.36e+08 Memory=  3939.753	t=     37.9 R=   1e+06
Depth=     495 States=  5.6e+07 Transitions= 1.38e+08 Memory=  4003.620	t=     38.6 R=   1e+06
Depth=     495 States=  5.7e+07 Transitions= 1.41e+08 Memory=  4059.284	t=     39.4 R=   1e+06
Depth=     495 States=  5.8e+07 Transitions= 1.43e+08 Memory=  4118.171	t=       40 R=   1e+06
Depth=     495 States=  5.9e+07 Transitions= 1.46e+08 Memory=  4179.011	t=     40.7 R=   1e+06
Depth=     495 States=    6e+07 Transitions= 1.48e+08 Memory=  4240.046	t=     41.4 R=   1e+06
Depth=     495 States=  6.1e+07 Transitions=  1.5e+08 Memory=  4299.616	t=       42 R=   1e+06
Depth=     495 States=  6.2e+07 Transitions= 1.53e+08 Memory=  4360.358	t=     42.8 R=   1e+06
Depth=     495 States=  6.3e+07 Transitions= 1.56e+08 Memory=  4421.296	t=     43.5 R=   1e+06
Depth=     495 States=  6.4e+07 Transitions= 1.58e+08 Memory=  4480.573	t=     44.2 R=   1e+06
Depth=     495 States=  6.5e+07 Transitions= 1.61e+08 Memory=  4541.120	t=     44.9 R=   1e+06
Depth=     495 States=  6.6e+07 Transitions= 1.64e+08 Memory=  4601.765	t=     45.7 R=   1e+06
Depth=     495 States=  6.7e+07 Transitions= 1.66e+08 Memory=  4662.605	t=     46.4 R=   1e+06
Depth=     495 States=  6.8e+07 Transitions= 1.69e+08 Memory=  4723.347	t=     47.1 R=   1e+06
Depth=     495 States=  6.9e+07 Transitions= 1.72e+08 Memory=  4783.308	t=     47.9 R=   1e+06
Depth=     495 States=    7e+07 Transitions= 1.75e+08 Memory=  4844.050	t=     48.6 R=   1e+06
Depth=     495 States=  7.1e+07 Transitions= 1.77e+08 Memory=  4904.792	t=     49.4 R=   1e+06
Depth=     495 States=  7.2e+07 Transitions=  1.8e+08 Memory=  4965.437	t=     50.1 R=   1e+06
Depth=     495 States=  7.3e+07 Transitions= 1.83e+08 Memory=  5026.081	t=     50.8 R=   1e+06
Depth=     495 States=  7.4e+07 Transitions= 1.86e+08 Memory=  5086.823	t=     51.6 R=   1e+06
Depth=     495 States=  7.5e+07 Transitions= 1.88e+08 Memory=  5147.370	t=     52.3 R=   1e+06
Depth=     495 States=  7.6e+07 Transitions=  1.9e+08 Memory=  5208.112	t=       53 R=   1e+06
Depth=     495 States=  7.7e+07 Transitions= 1.93e+08 Memory=  5268.659	t=     53.7 R=   1e+06
Depth=     495 States=  7.8e+07 Transitions= 1.96e+08 Memory=  5329.304	t=     54.4 R=   1e+06
Depth=     495 States=  7.9e+07 Transitions= 1.98e+08 Memory=  5389.851	t=     55.1 R=   1e+06
Depth=     495 States=    8e+07 Transitions= 2.01e+08 Memory=  5450.397	t=     55.8 R=   1e+06
Depth=     495 States=  8.1e+07 Transitions= 2.04e+08 Memory=  5510.847	t=     56.6 R=   1e+06
Depth=     495 States=  8.2e+07 Transitions= 2.07e+08 Memory=  5571.394	t=     57.4 R=   1e+06
Depth=     495 States=  8.3e+07 Transitions= 2.09e+08 Memory=  5631.940	t=     58.1 R=   1e+06
Depth=     495 States=  8.4e+07 Transitions= 2.12e+08 Memory=  5692.292	t=     58.9 R=   1e+06
Depth=     495 States=  8.5e+07 Transitions= 2.15e+08 Memory=  5752.937	t=     59.6 R=   1e+06
Depth=     495 States=  8.6e+07 Transitions= 2.17e+08 Memory=  5813.288	t=     60.4 R=   1e+06
Depth=     495 States=  8.7e+07 Transitions=  2.2e+08 Memory=  5873.640	t=     61.1 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
	+ Partial Order Reduction

Full statespace search for:
	never claim         	+ (eventually_execute)
	assertion violations	+ (if within scope of claim)
	acceptance   cycles 	+ (fairness disabled)
	invalid end states	- (disabled by never claim)

State-vector 136 byte, depth reached 495, errors: 0
 43696729 states, stored (8.73753e+07 visited)
1.3364574e+08 states, matched
2.2102101e+08 transitions (= visited+matched)
  3079804 atomic steps
hash conflicts:  42891875 (resolved)

Stats on memory usage (in Megabytes):
 6834.281	equivalent memory usage for states (stored*(State-vector + overhead))
 5385.290	actual memory usage for states (compression: 78.80%)
         	state-vector as stored = 101 byte + 28 byte overhead
  512.000	memory used for hash table (-w26)
    0.534	memory used for DFS stack (-m10000)
    1.636	memory lost to fragmentation
 5896.198	total actual memory usage



pan: elapsed time 61.4 seconds
pan: rate 1423977.7 states/second
```
