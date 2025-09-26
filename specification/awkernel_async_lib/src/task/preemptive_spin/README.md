# Preemptive fixed-priority scheduler that ensures priorities

## Intra-scheduler priority inversion

This is a model of the fully-preemptive `PrioritizedFIFOScheduler` to verify that priority inversion does not occur.
We have prepared an environment that could cause the priority inversion presented in [this comments](https://github.com/tier4/awkernel/pull/255#issuecomment-2556669740).
There are two CPUs and four tasks, and the smaller the task index, the higher the priority.
Tasks are executed as follows:

1. init: wake task 3
2. (CPU 0) worker thread 0: execute task 3, wake task 2, and block.
3. (CPU 1) worker thread 1: execute task 2, wake tasks 0,1, send IPI for preemption, and block.
4. interrupt_handler: handling IPI and occur preemption.
5. ...

### Targets

- [awkernel_async_lib/src/scheduler.rs](../../../../../awkernel_async_lib/src/scheduler.rs)
- [awkernel_async_lib/src/scheduler/prioritized_fifo.rs](../../../../../awkernel_async_lib/src/scheduler/prioritized_fifo.rs)
- [awkernel_async_lib/src/task/preempt.rs](../../../../../awkernel_async_lib/src/task/preempt.rs)
- [awkernel_async_lib/src/task.rs](../../../../../awkernel_async_lib/src/task.rs)

### Subjects to be Verified

1. The all tasks are eventually terminated (`ltl eventually_terminated`).
2. The waking processing of all tasks which includes preemption is eventually completed (`ltl eventually_prerequisites`).
3. The priority of tasks is ensured unless they are within the waking processing (`ltl ensure_priority`).

### Result

[Used Version](https://github.com/tier4/awkernel/commit/264fb9432d387d26810035177d08dc1283d13fd2)

`ltl eventually_terminated`

```
$ make run
spin -a preemptive.pml
ltl eventually_terminate: <> ((num_terminated==4))
gcc -O3 -DCOLLAPSE -DVECTORSZ=5000 -DNFAIR=3 -o pan pan.c
rm -f *.trail
./pan -a -n -m30000
Depth=    2473 States=    1e+06 Transitions= 2.44e+06 Memory=   166.071 t=     4.88 R=   2e+05
...
Depth=    2527 States= 5.15e+08 Transitions= 1.27e+09 Memory= 20232.670 t= 2.66e+03 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_terminate)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1180 byte, depth reached 2527, errors: 0
2.5767184e+08 states, stored (5.15344e+08 visited)
7.5537733e+08 states, matched
1.270721e+09 transitions (= visited+matched)
1.7736455e+08 atomic steps
hash conflicts: 2.3923657e+08 (resolved)

Stats on memory usage (in Megabytes):
298813.773      equivalent memory usage for states (stored*(State-vector + overhead))
18196.257       actual memory usage for states (compression: 6.09%)
                state-vector as stored = 38 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    1.803       memory lost to fragmentation
20244.591       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:3366120 2:1 3:9772 4:87352 5:99 6:1 ]

pan: elapsed time 2.66e+03 seconds
pan: rate 193485.09 states/second
```

`ltl eventually_prerequisites`

```
$ make run
rm -f pan.* *.trail pan *.tmp
spin -a preemptive.pml
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
gcc -O3 -DCOLLAPSE -DVECTORSZ=5000 -DNFAIR=3 -o pan pan.c
./pan -a -n -m30000
Depth=    2454 States=    1e+06 Transitions= 2.38e+06 Memory=   165.117 t=     5.35 R=   2e+05
...
Depth=    2552 States= 6.16e+08 Transitions=  1.7e+09 Memory= 40455.749 t= 4.28e+03 R=   1e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_prerequisites)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1180 byte, depth reached 2552, errors: 0
4.4340453e+08 states, stored (6.16007e+08 visited)
1.084581e+09 states, matched
1.7005877e+09 transitions (= visited+matched)
2.5654964e+08 atomic steps
hash conflicts: 3.6249904e+08 (resolved)

Stats on memory usage (in Megabytes):
514202.032      equivalent memory usage for states (stored*(State-vector + overhead))
32264.767       actual memory usage for states (compression: 6.27%)
                state-vector as stored = 40 byte + 36 byte overhead
 8192.000       memory used for hash table (-w30)
    1.831       memory used for DFS stack (-m30000)
    2.680       memory lost to fragmentation
40456.225       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:3482080 2:3 3:9772 4:90870 5:99 6:2 ]

pan: elapsed time 4.28e+03 seconds
pan: rate  143760.2 states/second
```

`ltl ensure_priority`

```
$ make run
rm -f pan.* *.trail pan *.tmp
spin -a preemptive.pml
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
gcc -O3 -DCOLLAPSE -DVECTORSZ=5000 -DNFAIR=3 -o pan pan.c
./pan -a -n -m30000
Depth=    2498 States=    1e+06 Transitions= 1.96e+06 Memory=   198.019 t=     4.08 R=   2e+05
...
Depth=    2552 States=  2.7e+08 Transitions= 5.32e+08 Memory= 21098.607 t= 1.25e+03 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (ensure_priority)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1180 byte, depth reached 2552, errors: 0
2.7080237e+08 states, stored
2.6291278e+08 states, matched
5.3371515e+08 transitions (= stored+matched)
 94638292 atomic steps
hash conflicts: 1.6658146e+08 (resolved)

Stats on memory usage (in Megabytes):
314040.834      equivalent memory usage for states (stored*(State-vector + overhead))
19112.501       actual memory usage for states (compression: 6.09%)
                state-vector as stored = 38 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    2.044       memory lost to fragmentation
21160.595       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:3439355 2:3 3:9772 4:90870 5:99 6:1 ]

pan: elapsed time 1.26e+03 seconds
pan: rate 215529.76 states/second
```

## Inter-scheduler priority inversion

As the above verification does not cover inter-scheduler priority inversion, we need to verify it separately. The model now supports multiple scheduler types through [this](https://github.com/tier4/awkernel/commit/4724e908cebeba5ab89ab21d310a309a6d892a00) changes: 

- Each task is assigned a `scheduler_type` field in `TaskInfo`.
- The system maintains separate `queue[SCHEDULER_TYPE_NUM]` for each scheduler type.
- The `wake_task()` placing tasks in their assigned scheduler type queue, `get_next_each_scheduler()` retrieving next task from a specific scheduler type, and `scheduler_get_next()` iterating through all scheduler types.

To keep the model less complex, please note the following abstractions compared to the Awkernel implementation:

- Even with different scheduler types, the same algorithm (`PrioritizedFIFOScheduler`) is used.
- For priority comparison, we use the simple priority value (`TaskInfo.id`) as before, rather than `combine_priority`.
  - This is ensured by guaranteeing that tasks with larger ids are never assigned to scheduler types with higher priority.

### First Results (The errors are found)

[Used Version](https://github.com/tier4/awkernel/commit/8ee41ca90485ed3360e4e4c0345d9882833be7cb)

The verification is failed as follows, because [this rule](https://github.com/tier4/awkernel/blob/108eb95a2ef8eddecf422b70c415f6b3f2310e59/awkernel_async_lib/src/scheduler/gedf.rs#L66) is violated for multi-scheduler environment. I will fix it later.

```
$ bash verify_all.bash 
===============================================================
Verifying with LTL=ensure_priority and sched_type_pattern=1
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula ensure_priority
Depth=    3099 States=    1e+06 Transitions= 1.97e+06 Memory=   198.973 t=     4.59 R=   2e+05
...
Depth=    3165 States=    8e+07 Transitions= 1.59e+08 Memory=  5944.737 t=      397 R=   2e+05
pan:1: assertion violated  !( !(( !(((((((((((((((waking[0]==0)&&(waking[1]==0))&&(waking[2]==0))&&(waking[3]==0))&&(q_len(ipi_requests[0])==0))&&(RUNNING[0]!= -(1)))&&(RUNNING[0]!=runnable_preempted_highest_priority))&&(q_len(ipi_requests[1])==0))&&(RUNNING[1]!= -(1)))&&(RUNNING[1]!=runnable_preempted_highest_priority))&& !(handling_interrupt[0]))&& !(handling_interrupt[1]))&& !(handling_interrupt[2]))&& !(handling_interrupt[3])))||(running_lowest_priority<runnable_preempted_highest_priority)))) (at depth 1631)
pan: wrote preemptive.pml.trail

(Spin Version 6.5.2 -- 6 December 2019)
Warning: Search not completed
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (ensure_priority)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1208 byte, depth reached 3165, errors: 1
 80763430 states, stored
 79489602 states, matched
1.6025303e+08 transitions (= stored+matched)
 25224570 atomic steps
hash conflicts:  47563491 (resolved)

Stats on memory usage (in Megabytes):
95815.379       equivalent memory usage for states (stored*(State-vector + overhead))
 5483.497       actual memory usage for states (compression: 5.72%)
                state-vector as stored = 35 byte + 36 byte overhead
  512.000       memory used for hash table (-w26)
    1.831       memory used for DFS stack (-m30000)
 5996.713       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:361011 2:3 3:2219 4:15079 5:103 8:1 ]

pan: elapsed time 401 seconds
pan: rate 201465.35 states/second
```

```
$ spin -t -DSCHED_TYPE_PATTERN=1 preemptive.pml
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
Never claim moves to line 22    [(1)]
              wake() call wake_task(): tid = 0,task = 3,state = Ready
              get_lowest_priority_task(): task = 3
              invoke_preemption() no need to preempt: hp_task = 3,lp_task = 0
              wake_task(): push to queue: tid = 0,task = 3
                                      proc 7 (run_main),tid = 1
                                      scheduler_get_next(): tid = 1,Chosen task = 3
                                      RUNNING[1] = 3
                                      future(): tid = 1, task = 3
                                      wake() call wake_task(): tid = 1,task = 2,state = Ready
                                      get_lowest_priority_task(): task = 2
                                      invoke_preemption() send IPI: hp_task = 2,lp_task = 3,lp_cpu_id = 1,interrupt_enabled[lp_cpu_id] = 0
                                  proc 6 (run_main),tid = 0
                      Received IPI request. cpu_id = 1
                      RUNNING[1] = 2
                      Preemption Occurs: cpu_id = 1,cur_task = 3,hp_task = 2
                      take_pooled_thread(): ret_tid = 2
                      context_switch(): cur_tid = 1,next_tid = 2
                                          proc 8 (run_main),tid = 2
                                          get_lowest_priority_task(): task = 3
                                          invoke_preemption() no need to preempt: hp_task = 3,lp_task = 2
                                          wake_task(): push to queue: tid = 2,task = 3
                                          RUNNING[1] = 2
                                          future(): tid = 2, task = 2
                                          wake() call wake_task(): tid = 2,task = 1,state = Ready
                                          get_lowest_priority_task(): task = 1
                                          invoke_preemption() send IPI: hp_task = 1,lp_task = 2,lp_cpu_id = 1,interrupt_enabled[lp_cpu_id] = 0
                                          wake() call wake_task(): tid = 2,task = 0,state = Ready
                                          get_lowest_priority_task(): task = 0
                                          invoke_preemption() send IPI: hp_task = 0,lp_task = 1,lp_cpu_id = 1,interrupt_enabled[lp_cpu_id] = 0
                                  scheduler_get_next(): tid = 0,Chosen task = 3
                          Received IPI request. cpu_id = 1
                          RUNNING[1] = 0
                          Preemption Occurs: cpu_id = 1,cur_task = 2,hp_task = 0
                          take_pooled_thread(): ret_tid = 3
                          context_switch(): cur_tid = 2,next_tid = 3
                                              proc 9 (run_main),tid = 3
                                              get_lowest_priority_task(): task = 2
                                              invoke_preemption() no need to preempt: hp_task = 2,lp_task = 0
                                              wake_task(): push to queue: tid = 3,task = 2
                                              RUNNING[1] = 0
                                              future(): tid = 3, task = 0
                                              RUNNING[1] = - 1
                                              result_future Ready: tid = 3,task = 0
                                              Terminated: tid = 3,task = 0,state = Terminated,num_terminated = 1,
                                              get_lowest_priority_task(): task = 1
                                              invoke_preemption() no need to preempt: hp_task = 1,lp_task = 0
                                              wake_task(): push to queue: tid = 3,task = 1
                                              scheduler_get_next(): tid = 3,Chosen task = 1
                                              RUNNING[1] = 1
                                              future(): tid = 3, task = 1
                                  RUNNING[0] = 3
Never claim moves to line 21    [(!((!(((((((((((((((waking[0]==0)&&(waking[1]==0))&&(waking[2]==0))&&(waking[3]==0))&&(len(ipi_requests[0])==0))&&(RUNNING[0]!=-(1)))&&(RUNNING[0]!=runnable_preempted_highest_priority))&&(len(ipi_requests[1])==0))&&(RUNNING[1]!=-(1)))&&(RUNNING[1]!=runnable_preempted_highest_priority))&&!(handling_interrupt[0]))&&!(handling_interrupt[1]))&&!(handling_interrupt[2]))&&!(handling_interrupt[3])))||(running_lowest_priority<runnable_preempted_highest_priority))))]
spin: _spin_nvr.tmp:21, Error: assertion violated
spin: text of failed assertion: assert(!(!((!(((((((((((((((waking[0]==0)&&(waking[1]==0))&&(waking[2]==0))&&(waking[3]==0))&&(len(ipi_requests[0])==0))&&(RUNNING[0]!=-(1)))&&(RUNNING[0]!=runnable_preempted_highest_priority))&&(len(ipi_requests[1])==0))&&(RUNNING[1]!=-(1)))&&(RUNNING[1]!=runnable_preempted_highest_priority))&&!(handling_interrupt[0]))&&!(handling_interrupt[1]))&&!(handling_interrupt[2]))&&!(handling_interrupt[3])))||(running_lowest_priority<runnable_preempted_highest_priority)))))
spin: trail ends after 1632 steps
```

### Results of Fixed Version

[Used Version](https://github.com/tier4/awkernel/pull/655/commits/a536ecfa06e0225a3b688c9cf13a356249664eae)

The Promela model was updated to solve inter-scheduler priority inversion by adding a new global mutex `lock_global_wake_get_mutex` to ensure atomic operations during critical scheduler interactions, i.e., `wake_task()` and `scheduler_get_next()`. There are no errors in the all verification.

```
===============================================================
Verifying with LTL=ensure_priority and sched_type_pattern=0
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula ensure_priority
Depth=    2521 States=    1e+06 Transitions= 1.95e+06 Memory=   199.926 t=     4.87 R=   2e+05
...
Depth=    2537 States= 1.51e+08 Transitions= 2.97e+08 Memory= 13056.271 t=      841 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (ensure_priority)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1216 byte, depth reached 2537, errors: 0
1.5199774e+08 states, stored
1.4726137e+08 states, matched
2.9925911e+08 transitions (= stored+matched)
 64924427 atomic steps
hash conflicts: 1.0527649e+08 (resolved)

Stats on memory usage (in Megabytes):
181485.341      equivalent memory usage for states (stored*(State-vector + overhead))
11076.686       actual memory usage for states (compression: 6.10%)
                state-vector as stored = 40 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    1.410       memory lost to fragmentation
13125.412       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:2234872 2:12 3:10244 4:99926 5:107 8:1 ]

pan: elapsed time 847 seconds
pan: rate 179530.55 states/second

===============================================================
Verifying with LTL=eventually_prerequisites and sched_type_pattern=0
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula eventually_prerequisites
Depth=    2399 States=    1e+06 Transitions= 2.36e+06 Memory=   166.548 t=     5.62 R=   2e+05
...
Depth=    2537 States= 3.52e+08 Transitions= 9.75e+08 Memory= 19733.899 t= 2.51e+03 R=   1e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_prerequisites)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1216 byte, depth reached 2537, errors: 0
2.5216786e+08 states, stored (3.52338e+08 visited)
6.2338335e+08 states, matched
9.7572132e+08 transitions (= visited+matched)
1.9231417e+08 atomic steps
hash conflicts: 2.239899e+08 (resolved)

Stats on memory usage (in Megabytes):
301088.483      equivalent memory usage for states (stored*(State-vector + overhead))
17700.405       actual memory usage for states (compression: 5.88%)
                state-vector as stored = 38 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    1.384       memory lost to fragmentation
19749.157       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:2372787 2:12 3:10244 4:99926 5:107 7:2 ]

pan: elapsed time 2.51e+03 seconds
pan: rate 140471.63 states/second

===============================================================
Verifying with LTL=eventually_terminate and sched_type_pattern=0
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula eventually_terminate
Depth=    2496 States=    1e+06 Transitions= 2.43e+06 Memory=   167.501 t=     5.79 R=   2e+05
...
Depth=    2512 States= 2.91e+08 Transitions= 7.17e+08 Memory= 12709.610 t=  1.8e+03 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_terminate)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1216 byte, depth reached 2512, errors: 0
1.4578084e+08 states, stored (2.91562e+08 visited)
4.2640196e+08 states, matched
7.1796364e+08 transitions (= visited+matched)
1.2395589e+08 atomic steps
hash conflicts: 1.4005791e+08 (resolved)

Stats on memory usage (in Megabytes):
174062.359      equivalent memory usage for states (stored*(State-vector + overhead))
10679.490       actual memory usage for states (compression: 6.14%)
                state-vector as stored = 41 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
12728.684       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:2326966 2:8 3:10244 4:97573 5:107 6:1 ]

pan: elapsed time 1.8e+03 seconds
pan: rate 161671.54 states/second

===============================================================
Verifying with LTL=ensure_priority and sched_type_pattern=1
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula ensure_priority
Depth=    2584 States=    1e+06 Transitions= 1.95e+06 Memory=   199.926 t=     4.85 R=   2e+05
...
Depth=    2600 States=  1.6e+08 Transitions= 3.15e+08 Memory= 13661.377 t=      884 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (ensure_priority)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1216 byte, depth reached 2600, errors: 0
1.6056036e+08 states, stored
1.5560281e+08 states, matched
3.1616317e+08 transitions (= stored+matched)
 67761969 atomic steps
hash conflicts: 1.0781288e+08 (resolved)

Stats on memory usage (in Megabytes):
191709.111      equivalent memory usage for states (stored*(State-vector + overhead))
11651.303       actual memory usage for states (compression: 6.08%)
                state-vector as stored = 40 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    1.445       memory lost to fragmentation
13700.001       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:2279607 2:12 3:10244 4:99926 5:107 8:1 ]

pan: elapsed time 887 seconds
pan: rate 180941.63 states/second

===============================================================
Verifying with LTL=eventually_prerequisites and sched_type_pattern=1
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula eventually_prerequisites
Depth=    2462 States=    1e+06 Transitions= 2.36e+06 Memory=   166.071 t=     5.59 R=   2e+05
...
Depth=    2600 States= 3.69e+08 Transitions= 1.02e+09 Memory= 20566.933 t= 2.61e+03 R=   1e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_prerequisites)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1216 byte, depth reached 2600, errors: 0
2.6514649e+08 states, stored (3.69733e+08 visited)
6.5238061e+08 states, matched
1.0221132e+09 transitions (= visited+matched)
1.9962294e+08 atomic steps
hash conflicts: 2.3518003e+08 (resolved)

Stats on memory usage (in Megabytes):
316584.970      equivalent memory usage for states (stored*(State-vector + overhead))
18558.696       actual memory usage for states (compression: 5.86%)
                state-vector as stored = 37 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    1.852       memory lost to fragmentation
20606.987       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:2385079 2:12 3:10244 4:99926 5:107 7:2 ]

pan: elapsed time 2.61e+03 seconds
pan: rate 141555.33 states/second

===============================================================
Verifying with LTL=eventually_terminate and sched_type_pattern=1
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula eventually_terminate
Depth=    2559 States=    1e+06 Transitions= 2.43e+06 Memory=   167.501 t=      5.8 R=   2e+05
...
Depth=    2575 States= 3.08e+08 Transitions= 7.59e+08 Memory= 13280.861 t= 1.89e+03 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_terminate)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1216 byte, depth reached 2575, errors: 0
1.5434346e+08 states, stored (3.08687e+08 visited)
4.5164746e+08 states, matched
7.6033438e+08 transitions (= visited+matched)
1.2963097e+08 atomic steps
hash conflicts: 1.474679e+08 (resolved)

Stats on memory usage (in Megabytes):
184286.129      equivalent memory usage for states (stored*(State-vector + overhead))
11255.509       actual memory usage for states (compression: 6.11%)
                state-vector as stored = 40 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    1.424       memory lost to fragmentation
13304.226       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:2372745 2:8 3:10244 4:97573 5:107 6:1 ]

pan: elapsed time 1.9e+03 seconds
pan: rate 162877.42 states/second

===============================================================
Verifying with LTL=ensure_priority and sched_type_pattern=2
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula ensure_priority
Depth=    2605 States=    1e+06 Transitions= 1.95e+06 Memory=   199.926 t=     4.85 R=   2e+05
...
Depth=    2621 States= 1.65e+08 Transitions= 3.25e+08 Memory= 13996.594 t=      914 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (ensure_priority)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1216 byte, depth reached 2621, errors: 0
1.6590364e+08 states, stored
1.6078225e+08 states, matched
3.2668589e+08 transitions (= stored+matched)
 69309657 atomic steps
hash conflicts: 1.1019065e+08 (resolved)

Stats on memory usage (in Megabytes):
198088.989      equivalent memory usage for states (stored*(State-vector + overhead))
12009.880       actual memory usage for states (compression: 6.06%)
                state-vector as stored = 40 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    1.443       memory lost to fragmentation
14058.583       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:2303822 2:12 3:10244 4:99926 5:107 8:1 ]

pan: elapsed time 919 seconds
pan: rate 180477.17 states/second

===============================================================
Verifying with LTL=eventually_prerequisites and sched_type_pattern=2
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula eventually_prerequisites
Depth=    2462 States=    1e+06 Transitions= 2.35e+06 Memory=   166.071 t=     5.62 R=   2e+05
...
Depth=    2621 States=  3.8e+08 Transitions= 1.05e+09 Memory= 21112.912 t= 2.71e+03 R=   1e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_prerequisites)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1216 byte, depth reached 2621, errors: 0
2.7328853e+08 states, stored (3.80673e+08 visited)
6.7071401e+08 states, matched
1.0513874e+09 transitions (= visited+matched)
2.035583e+08 atomic steps
hash conflicts: 2.4233126e+08 (resolved)

Stats on memory usage (in Megabytes):
326306.568      equivalent memory usage for states (stored*(State-vector + overhead))
19099.799       actual memory usage for states (compression: 5.85%)
                state-vector as stored = 37 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    1.747       memory lost to fragmentation
21148.198       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:2398685 2:12 3:10244 4:99926 5:107 7:2 ]

pan: elapsed time 2.71e+03 seconds
pan: rate 140251.49 states/second

===============================================================
Verifying with LTL=eventually_terminate and sched_type_pattern=2
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula eventually_terminate
Depth=    2514 States=    1e+06 Transitions= 2.42e+06 Memory=   167.025 t=     5.84 R=   2e+05
...
Depth=    2596 States= 3.19e+08 Transitions= 7.86e+08 Memory= 13650.887 t= 1.96e+03 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_terminate)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1216 byte, depth reached 2596, errors: 0
1.5968674e+08 states, stored (3.19373e+08 visited)
4.6734962e+08 states, matched
7.867231e+08 transitions (= visited+matched)
1.3272635e+08 atomic steps
hash conflicts: 1.5217597e+08 (resolved)

Stats on memory usage (in Megabytes):
190666.007      equivalent memory usage for states (stored*(State-vector + overhead))
11615.225       actual memory usage for states (compression: 6.09%)
                state-vector as stored = 40 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    1.607       memory lost to fragmentation
13663.762       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:2398642 2:8 3:10244 4:97573 5:107 6:1 ]

pan: elapsed time 1.96e+03 seconds
pan: rate 162755.49 states/second

===============================================================
Verifying with LTL=ensure_priority and sched_type_pattern=3
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula ensure_priority
Depth=    2605 States=    1e+06 Transitions= 1.95e+06 Memory=   199.926 t=     4.86 R=   2e+05
...
Depth=    2621 States= 1.66e+08 Transitions= 3.27e+08 Memory= 14063.828 t=      922 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (ensure_priority)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1216 byte, depth reached 2621, errors: 0
1.6659906e+08 states, stored
1.6142545e+08 states, matched
3.2802451e+08 transitions (= stored+matched)
 69507259 atomic steps
hash conflicts: 1.1052438e+08 (resolved)

Stats on memory usage (in Megabytes):
198919.321      equivalent memory usage for states (stored*(State-vector + overhead))
12056.346       actual memory usage for states (compression: 6.06%)
                state-vector as stored = 40 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    1.179       memory lost to fragmentation
14105.313       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:2308890 2:12 3:10244 4:99926 5:107 8:1 ]

pan: elapsed time 926 seconds
pan: rate 179976.73 states/second

===============================================================
Verifying with LTL=eventually_prerequisites and sched_type_pattern=3
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula eventually_prerequisites
Depth=    2462 States=    1e+06 Transitions= 2.35e+06 Memory=   166.071 t=     5.61 R=   2e+05
...
Depth=    2621 States= 3.81e+08 Transitions= 1.05e+09 Memory= 21163.933 t=  2.7e+03 R=   1e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_prerequisites)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1216 byte, depth reached 2621, errors: 0
2.7420845e+08 states, stored (3.81818e+08 visited)
6.7227963e+08 states, matched
1.0540975e+09 transitions (= visited+matched)
2.0391055e+08 atomic steps
hash conflicts: 2.4299923e+08 (resolved)

Stats on memory usage (in Megabytes):
327404.953      equivalent memory usage for states (stored*(State-vector + overhead))
19160.768       actual memory usage for states (compression: 5.85%)
                state-vector as stored = 37 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    1.681       memory lost to fragmentation
21209.233       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:2403040 2:12 3:10244 4:99926 5:107 7:2 ]

pan: elapsed time 2.7e+03 seconds
pan: rate 141177.15 states/second

===============================================================
Verifying with LTL=eventually_terminate and sched_type_pattern=3
===============================================================
ltl eventually_terminate: <> ((num_terminated==4))
ltl eventually_prerequisites: [] (<> (((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))))
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((len(ipi_requests[1])==0))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[1]!=runnable_preempted_highest_priority))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3])))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
  the model contains 3 never claims: ensure_priority, eventually_prerequisites, eventually_terminate
  only one claim is used in a verification run
  choose which one with ./pan -a -N name (defaults to -N eventually_terminate)
  or use e.g.: spin -search -ltl eventually_terminate mutex.pml
pan: ltl formula eventually_terminate
Depth=    2514 States=    1e+06 Transitions= 2.42e+06 Memory=   167.025 t=     5.76 R=   2e+05
...
Depth=    2596 States=  3.2e+08 Transitions= 7.88e+08 Memory= 13684.266 t= 1.97e+03 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_terminate)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1216 byte, depth reached 2596, errors: 0
1.6038216e+08 states, stored (3.20764e+08 visited)
4.6933144e+08 states, matched
7.9009576e+08 transitions (= visited+matched)
1.3312155e+08 atomic steps
hash conflicts: 1.5295385e+08 (resolved)

Stats on memory usage (in Megabytes):
191496.338      equivalent memory usage for states (stored*(State-vector + overhead))
11661.187       actual memory usage for states (compression: 6.09%)
                state-vector as stored = 40 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    1.831       memory used for DFS stack (-m30000)
    1.316       memory lost to fragmentation
13710.015       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:2404383 2:8 3:10244 4:97573 5:107 6:1 ]

pan: elapsed time 1.97e+03 seconds
pan: rate  162512.7 states/second
```
