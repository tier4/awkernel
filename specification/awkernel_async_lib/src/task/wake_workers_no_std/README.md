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
Depth=     727 States=    1e+06 Transitions= 1.61e+06 Memory=   160.468	t=     0.63 R=   2e+06
Depth=     727 States=    2e+06 Transitions= 3.31e+06 Memory=   192.304	t=     1.31 R=   2e+06
Depth=     727 States=    3e+06 Transitions= 4.99e+06 Memory=   215.155	t=     1.99 R=   2e+06
Depth=     727 States=    4e+06 Transitions= 6.71e+06 Memory=   241.034	t=     2.68 R=   1e+06
Depth=     727 States=    5e+06 Transitions= 8.43e+06 Memory=   263.788	t=     3.38 R=   1e+06
Depth=     727 States=    6e+06 Transitions= 1.01e+07 Memory=   291.034	t=     4.06 R=   1e+06
Depth=     727 States=    7e+06 Transitions= 1.19e+07 Memory=   317.108	t=     4.75 R=   1e+06
Depth=     727 States=    8e+06 Transitions= 1.38e+07 Memory=   343.964	t=     5.53 R=   1e+06
Depth=     755 States=    9e+06 Transitions= 1.56e+07 Memory=   370.917	t=     6.27 R=   1e+06
Depth=     755 States=    1e+07 Transitions= 1.74e+07 Memory=   404.315	t=        7 R=   1e+06
Depth=     789 States=  1.1e+07 Transitions= 1.91e+07 Memory=   433.417	t=     7.75 R=   1e+06
Depth=     789 States=  1.2e+07 Transitions= 2.08e+07 Memory=   460.272	t=     8.51 R=   1e+06
Depth=     795 States=  1.3e+07 Transitions= 2.27e+07 Memory=   486.933	t=     9.24 R=   1e+06
Depth=     843 States=  1.4e+07 Transitions= 2.45e+07 Memory=   513.886	t=     9.98 R=   1e+06
Depth=     843 States=  1.5e+07 Transitions= 2.66e+07 Memory=   540.448	t=     10.8 R=   1e+06
Depth=     843 States=  1.6e+07 Transitions= 2.85e+07 Memory=   558.222	t=     11.5 R=   1e+06
Depth=     843 States=  1.7e+07 Transitions= 3.02e+07 Memory=   585.565	t=     12.3 R=   1e+06
Depth=     843 States=  1.8e+07 Transitions=  3.2e+07 Memory=   612.909	t=     13.1 R=   1e+06
Depth=     843 States=  1.9e+07 Transitions= 3.38e+07 Memory=   640.155	t=       14 R=   1e+06
Depth=     885 States=    2e+07 Transitions= 3.56e+07 Memory=   666.522	t=     14.8 R=   1e+06
Depth=     885 States=  2.1e+07 Transitions= 3.74e+07 Memory=   692.694	t=     15.6 R=   1e+06
Depth=     885 States=  2.2e+07 Transitions= 3.94e+07 Memory=   719.550	t=     16.3 R=   1e+06
Depth=     885 States=  2.3e+07 Transitions= 4.16e+07 Memory=   745.819	t=     17.2 R=   1e+06
Depth=     885 States=  2.4e+07 Transitions= 4.37e+07 Memory=   773.456	t=       18 R=   1e+06
Depth=     885 States=  2.5e+07 Transitions= 4.55e+07 Memory=   816.815	t=     18.9 R=   1e+06
Depth=     885 States=  2.6e+07 Transitions= 4.76e+07 Memory=   829.901	t=     19.7 R=   1e+06
Depth=     885 States=  2.7e+07 Transitions= 4.95e+07 Memory=   856.952	t=     20.6 R=   1e+06
Depth=     885 States=  2.8e+07 Transitions= 5.15e+07 Memory=   880.292	t=     21.4 R=   1e+06
Depth=     885 States=  2.9e+07 Transitions= 5.36e+07 Memory=   907.050	t=     22.2 R=   1e+06
Depth=     885 States=    3e+07 Transitions= 5.56e+07 Memory=   933.808	t=     23.1 R=   1e+06
Depth=     885 States=  3.1e+07 Transitions= 5.76e+07 Memory=   963.007	t=     23.9 R=   1e+06
Depth=     885 States=  3.2e+07 Transitions= 5.98e+07 Memory=   990.058	t=     24.7 R=   1e+06
Depth=     885 States=  3.3e+07 Transitions= 6.21e+07 Memory=  1014.276	t=     25.6 R=   1e+06
Depth=     885 States=  3.4e+07 Transitions= 6.43e+07 Memory=  1041.522	t=     26.6 R=   1e+06
pan: resizing hashtable to -w26..  done
Depth=     885 States=  3.5e+07 Transitions= 6.67e+07 Memory=  1563.776	t=     28.3 R=   1e+06
Depth=     885 States=  3.6e+07 Transitions=  6.9e+07 Memory=  1590.632	t=     29.1 R=   1e+06
Depth=     885 States=  3.7e+07 Transitions=  7.1e+07 Memory=  1617.683	t=     29.9 R=   1e+06
Depth=     885 States=  3.8e+07 Transitions= 7.33e+07 Memory=  1644.050	t=     30.8 R=   1e+06
Depth=     885 States=  3.9e+07 Transitions= 7.54e+07 Memory=  1670.319	t=     31.6 R=   1e+06
Depth=     885 States=    4e+07 Transitions= 7.75e+07 Memory=  1697.370	t=     32.3 R=   1e+06
Depth=     885 States=  4.1e+07 Transitions= 7.98e+07 Memory=  1723.835	t=     33.2 R=   1e+06
Depth=     899 States=  4.2e+07 Transitions= 8.18e+07 Memory=  1752.351	t=       34 R=   1e+06
Depth=     961 States=  4.3e+07 Transitions=  8.4e+07 Memory=  1779.401	t=     34.8 R=   1e+06
Depth=     961 States=  4.4e+07 Transitions= 8.63e+07 Memory=  1805.183	t=     35.7 R=   1e+06
Depth=     961 States=  4.5e+07 Transitions= 8.86e+07 Memory=  1831.159	t=     36.5 R=   1e+06
Depth=     961 States=  4.6e+07 Transitions= 9.08e+07 Memory=  1858.112	t=     37.4 R=   1e+06
Depth=     961 States=  4.7e+07 Transitions=  9.3e+07 Memory=  1884.480	t=     38.2 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
	+ Partial Order Reduction
	+ Compression

Full statespace search for:
	never claim         	+ (eventually_execute)
	assertion violations	+ (if within scope of claim)
	acceptance   cycles 	+ (fairness disabled)
	invalid end states	- (disabled by never claim)

State-vector 96 byte, depth reached 961, errors: 0
 23943382 states, stored (4.78868e+07 visited)
 47043132 states, matched
 94929894 transitions (= visited+matched)
 16797976 atomic steps
hash conflicts:  18006062 (resolved)

Stats on memory usage (in Megabytes):
 3014.113	equivalent memory usage for states (stored*(State-vector + overhead))
 1396.063	actual memory usage for states (compression: 46.32%)
         	state-vector as stored = 25 byte + 36 byte overhead
  512.000	memory used for hash table (-w26)
    0.534	memory used for DFS stack (-m10000)
 1908.112	total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:79123 2:78 3:271 4:3 5:44 6:2 ]

pan: elapsed time 38.9 seconds
pan: rate 1230073.5 states/second
```
