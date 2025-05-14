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
Depth=     635 States=    1e+06 Transitions= 1.57e+06 Memory=   157.733	t=     0.61 R=   2e+06
Depth=     753 States=    2e+06 Transitions= 3.21e+06 Memory=   200.605	t=     1.28 R=   2e+06
Depth=     753 States=    3e+06 Transitions= 4.87e+06 Memory=   216.034	t=     1.94 R=   2e+06
Depth=     753 States=    4e+06 Transitions= 6.51e+06 Memory=   239.862	t=      2.6 R=   2e+06
Depth=     753 States=    5e+06 Transitions= 8.22e+06 Memory=   267.987	t=     3.28 R=   2e+06
Depth=     753 States=    6e+06 Transitions=  9.9e+06 Memory=   290.155	t=     3.95 R=   2e+06
Depth=     753 States=    7e+06 Transitions= 1.16e+07 Memory=   317.108	t=     4.61 R=   2e+06
Depth=     753 States=    8e+06 Transitions= 1.34e+07 Memory=   343.964	t=     5.29 R=   2e+06
Depth=     753 States=    9e+06 Transitions= 1.52e+07 Memory=   371.112	t=     5.99 R=   2e+06
Depth=     779 States=    1e+07 Transitions=  1.7e+07 Memory=   397.480	t=     6.67 R=   1e+06
Depth=     779 States=  1.1e+07 Transitions= 1.88e+07 Memory=   424.335	t=     7.37 R=   1e+06
Depth=     815 States=  1.2e+07 Transitions= 2.04e+07 Memory=   462.714	t=     8.06 R=   1e+06
Depth=     815 States=  1.3e+07 Transitions= 2.21e+07 Memory=   488.105	t=     8.78 R=   1e+06
Depth=     815 States=  1.4e+07 Transitions= 2.39e+07 Memory=   514.765	t=      9.5 R=   1e+06
Depth=     873 States=  1.5e+07 Transitions= 2.57e+07 Memory=   541.620	t=     10.2 R=   1e+06
Depth=     873 States=  1.6e+07 Transitions= 2.75e+07 Memory=   568.378	t=     10.9 R=   1e+06
Depth=     873 States=  1.7e+07 Transitions= 2.95e+07 Memory=   595.331	t=     11.7 R=   1e+06
Depth=     873 States=  1.8e+07 Transitions= 3.15e+07 Memory=   612.812	t=     12.5 R=   1e+06
Depth=     873 States=  1.9e+07 Transitions= 3.32e+07 Memory=   644.745	t=     13.2 R=   1e+06
Depth=     873 States=    2e+07 Transitions= 3.49e+07 Memory=   671.112	t=       14 R=   1e+06
Depth=     873 States=  2.1e+07 Transitions= 3.66e+07 Memory=   692.890	t=     14.7 R=   1e+06
Depth=     913 States=  2.2e+07 Transitions= 3.84e+07 Memory=   719.843	t=     15.5 R=   1e+06
Depth=     913 States=  2.3e+07 Transitions= 4.02e+07 Memory=   746.405	t=     16.2 R=   1e+06
Depth=     913 States=  2.4e+07 Transitions=  4.2e+07 Memory=   773.163	t=       17 R=   1e+06
Depth=     913 States=  2.5e+07 Transitions= 4.41e+07 Memory=   800.116	t=     17.8 R=   1e+06
Depth=     913 States=  2.6e+07 Transitions= 4.62e+07 Memory=   827.167	t=     18.6 R=   1e+06
Depth=     913 States=  2.7e+07 Transitions= 4.82e+07 Memory=   853.241	t=     19.4 R=   1e+06
Depth=     913 States=  2.8e+07 Transitions=    5e+07 Memory=   899.433	t=     20.2 R=   1e+06
Depth=     913 States=  2.9e+07 Transitions= 5.21e+07 Memory=   914.081	t=     21.1 R=   1e+06
Depth=     913 States=    3e+07 Transitions=  5.4e+07 Memory=   945.331	t=       22 R=   1e+06
Depth=     913 States=  3.1e+07 Transitions=  5.6e+07 Memory=   960.565	t=     22.8 R=   1e+06
Depth=     913 States=  3.2e+07 Transitions= 5.79e+07 Memory=   987.519	t=     23.5 R=   1e+06
Depth=     913 States=  3.3e+07 Transitions= 5.99e+07 Memory=  1014.374	t=     24.4 R=   1e+06
Depth=     913 States=  3.4e+07 Transitions= 6.19e+07 Memory=  1041.620	t=     25.2 R=   1e+06
pan: resizing hashtable to -w26..  done
Depth=     913 States=  3.5e+07 Transitions= 6.39e+07 Memory=  1564.460	t=     26.8 R=   1e+06
Depth=     913 States=  3.6e+07 Transitions= 6.61e+07 Memory=  1590.730	t=     27.6 R=   1e+06
Depth=     913 States=  3.7e+07 Transitions= 6.84e+07 Memory=  1617.585	t=     28.4 R=   1e+06
Depth=     913 States=  3.8e+07 Transitions= 7.06e+07 Memory=  1645.612	t=     29.3 R=   1e+06
Depth=     913 States=  3.9e+07 Transitions= 7.29e+07 Memory=  1671.198	t=     30.1 R=   1e+06
Depth=     913 States=    4e+07 Transitions= 7.53e+07 Memory=  1697.956	t=     30.9 R=   1e+06
Depth=     913 States=  4.1e+07 Transitions= 7.73e+07 Memory=  1724.909	t=     31.7 R=   1e+06
Depth=     913 States=  4.2e+07 Transitions= 7.94e+07 Memory=  1751.667	t=     32.6 R=   1e+06
Depth=     913 States=  4.3e+07 Transitions= 8.16e+07 Memory=  1777.839	t=     33.4 R=   1e+06
Depth=     913 States=  4.4e+07 Transitions= 8.37e+07 Memory=  1804.694	t=     34.1 R=   1e+06
Depth=     913 States=  4.5e+07 Transitions= 8.57e+07 Memory=  1831.159	t=     34.9 R=   1e+06
Depth=     913 States=  4.6e+07 Transitions=  8.8e+07 Memory=  1859.772	t=     35.8 R=   1e+06
Depth=     981 States=  4.7e+07 Transitions= 8.99e+07 Memory=  1886.726	t=     36.5 R=   1e+06
Depth=     995 States=  4.8e+07 Transitions= 9.22e+07 Memory=  1913.679	t=     37.3 R=   1e+06
Depth=     995 States=  4.9e+07 Transitions= 9.45e+07 Memory=  1939.460	t=     38.2 R=   1e+06
Depth=     995 States=    5e+07 Transitions= 9.67e+07 Memory=  1965.339	t=       39 R=   1e+06
Depth=     995 States=  5.1e+07 Transitions= 9.89e+07 Memory=  1991.901	t=     39.8 R=   1e+06
Depth=     995 States=  5.2e+07 Transitions= 1.01e+08 Memory=  2018.952	t=     40.6 R=   1e+06
Depth=     995 States=  5.3e+07 Transitions= 1.03e+08 Memory=  2045.905	t=     41.5 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
	+ Partial Order Reduction
	+ Compression

Full statespace search for:
	never claim         	+ (eventually_execute)
	assertion violations	+ (if within scope of claim)
	acceptance   cycles 	+ (fairness disabled)
	invalid end states	- (disabled by never claim)

State-vector 96 byte, depth reached 995, errors: 0
 26809921 states, stored (5.36198e+07 visited)
 50913343 states, matched
1.0453318e+08 transitions (= visited+matched)
 17581296 atomic steps
hash conflicts:  19371171 (resolved)

Stats on memory usage (in Megabytes):
 3374.967	equivalent memory usage for states (stored*(State-vector + overhead))
 1549.863	actual memory usage for states (compression: 45.92%)
         	state-vector as stored = 25 byte + 36 byte overhead
  512.000	memory used for hash table (-w26)
    0.534	memory used for DFS stack (-m10000)
 2061.921	total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:92365 2:84 3:292 4:3 5:44 6:2 ]

pan: elapsed time 42 seconds
pan: rate 1278184.5 states/second
```
