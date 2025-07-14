# Preemptive fixed-priority scheduler that ensures priorities

This is a model of the fully-preemptive `PrioritizedFIFOScheduler` to verify that priority inversion does not occur.
Note that this does not consider inter-scheduler preemption.
We have prepared an environment that could cause the priority inversion presented in [this comments](https://github.com/tier4/awkernel/pull/255#issuecomment-2556669740).
There are two CPUs and four tasks, and the smaller the task index, the higher the priority.
Tasks are executed as follows:

1. init: wake task 3
2. (CPU 0) worker thread 0: execute task 3, wake task 2, and block.
3. (CPU 1) worker thread 1: execute task 2, wake tasks 1,0, send IPI for preemption, and block.
4. interrupt_handler: handling IPI and occur preemption.
5. ...

## Targets

- [awkernel_async_lib/src/scheduler.rs](../../../../../awkernel_async_lib/src/scheduler.rs)
- [awkernel_async_lib/src/scheduler/prioritized_fifo.rs](../../../../../awkernel_async_lib/src/scheduler/prioritized_fifo.rs)
- [awkernel_async_lib/src/task/preempt.rs](../../../../../awkernel_async_lib/src/task/preempt.rs)
- [awkernel_async_lib/src/task.rs](../../../../../awkernel_async_lib/src/task.rs)

## Subjects to be Verified

1. The waking processing of all tasks which includes preemption is eventually completed (`ltl eventually_prerequisites`).
2. The priority of tasks is ensured unless they are within the waking processing (`ltl ensure_priority`).

## Result

`ltl eventually_prerequisites`

```
$ make run
spin -a preemptive.pml
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
gcc -O3 -DVECTORSZ=5000 -DNFAIR=3 -o pan pan.c
rm -f *.trail
./pan -a -n -m30000
Depth=    2181 States=    1e+06 Transitions= 2.35e+06 Memory=   627.649 t=     3.74 R=   3e+05
Depth=    2182 States=    2e+06 Transitions= 4.72e+06 Memory=  1124.037 t=     7.46 R=   3e+05
Depth=    2182 States=    3e+06 Transitions= 7.15e+06 Memory=  1620.901 t=     11.3 R=   3e+05
Depth=    2270 States=    4e+06 Transitions= 9.53e+06 Memory=  2278.459 t=     15.3 R=   3e+05
Depth=    2270 States=    5e+06 Transitions=  1.2e+07 Memory=  3271.711 t=     19.8 R=   3e+05
Depth=    2270 States=    6e+06 Transitions= 1.45e+07 Memory=  4264.963 t=     24.4 R=   2e+05
Depth=    2270 States=    7e+06 Transitions=  1.8e+07 Memory=  5258.215 t=     30.5 R=   2e+05
Depth=    2383 States=    8e+06 Transitions=  2.1e+07 Memory=  5965.841 t=     35.6 R=   2e+05
Depth=    2472 States=    9e+06 Transitions= 2.33e+07 Memory=  6770.742 t=     39.5 R=   2e+05
Depth=    2475 States=    1e+07 Transitions= 2.61e+07 Memory=  7700.575 t=     44.4 R=   2e+05
Depth=    2475 States=  1.1e+07 Transitions= 2.87e+07 Memory=  8266.581 t=     48.7 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (eventually_prerequisites)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1052 byte, depth reached 2475, errors: 0
  8538300 states, stored (1.13485e+07 visited)
 18758576 states, matched
 30107063 transitions (= visited+matched)
 46911550 atomic steps
hash conflicts:   2525539 (resolved)

Stats on memory usage (in Megabytes):
 8794.178       equivalent memory usage for states (stored*(State-vector + overhead))
 8495.650       actual memory usage for states (compression: 96.61%)
                state-vector as stored = 1015 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    1.831       memory used for DFS stack (-m30000)
   13.696       memory lost to fragmentation
 8611.811       total actual memory usage



pan: elapsed time 51.1 seconds
pan: rate 222083.89 states/second
```

`ltl ensure_priority`

```
$ make run
spin -a preemptive.pml
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((RUNNING[1]!=runnable_preempted_highest_priority)))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
gcc -O3 -DVECTORSZ=5000 -DNFAIR=3 -o pan pan.c
rm -f *.trail
./pan -a -n -m30000
Depth=    2270 States=    1e+06 Transitions= 1.95e+06 Memory=  1123.560 t=     3.58 R=   3e+05
Depth=    2270 States=    2e+06 Transitions= 3.92e+06 Memory=  2116.812 t=      7.2 R=   3e+05
Depth=    2270 States=    3e+06 Transitions= 5.89e+06 Memory=  3110.063 t=     10.8 R=   3e+05
Depth=    2285 States=    4e+06 Transitions= 7.87e+06 Memory=  4103.792 t=     14.5 R=   3e+05
Depth=    2475 States=    5e+06 Transitions= 9.83e+06 Memory=  5097.044 t=     18.3 R=   3e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (ensure_priority)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1052 byte, depth reached 2475, errors: 0
  5728113 states, stored
  5542212 states, matched
 11270325 transitions (= stored+matched)
 18548841 atomic steps
hash conflicts:    480693 (resolved)

Stats on memory usage (in Megabytes):
 5899.775       equivalent memory usage for states (stored*(State-vector + overhead))
 5699.308       actual memory usage for states (compression: 96.60%)
                state-vector as stored = 1015 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    1.831       memory used for DFS stack (-m30000)
    9.236       memory lost to fragmentation
 5819.929       total actual memory usage



pan: elapsed time 21 seconds
pan: rate 272378.17 states/second
```
