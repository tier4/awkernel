# Cooperative Multitasking

## Targets

- [awkernel_async_lib/src/task.rs](../../../../../awkernel_async_lib/src/task.rs).
- [awkernel_async_lib/src/scheduler/fifo.rs](../../../../../awkernel_async_lib/src/scheduler/fifo.rs).

## Subjects to be Verified

1. The scheduler is deadlock- and starvation-free.
2. If a task is awakened by other task, the task will be eventually executed.
3. The scheduler is fair.

## Result

### Eventually Terminated (Subject 1 and 2)

```
spin -a cooperative.pml
ltl p0: <> ((num_terminated==4))
gcc -O3 -o pan pan.c
./pan -f -a -m1000000000
Depth=    1504 States=    1e+06 Transitions= 1.86e+06 Memory= 53611.594 t=     0.88 R=   1e+06
Depth=    1526 States=    2e+06 Transitions= 3.73e+06 Memory= 53689.035 t=     1.76 R=   1e+06
Depth=    1721 States=    3e+06 Transitions= 5.57e+06 Memory= 53766.770 t=     2.63 R=   1e+06
Depth=    1721 States=    4e+06 Transitions=  7.4e+06 Memory= 53844.602 t=      3.5 R=   1e+06
Depth=    1721 States=    5e+06 Transitions= 9.24e+06 Memory= 53922.922 t=     4.37 R=   1e+06
Depth=    1721 States=    6e+06 Transitions= 1.11e+07 Memory= 54001.340 t=     5.23 R=   1e+06
Depth=    1946 States=    7e+06 Transitions= 1.29e+07 Memory= 54079.465 t=     6.11 R=   1e+06
Depth=    1946 States=    8e+06 Transitions= 1.47e+07 Memory= 54157.688 t=     6.98 R=   1e+06
Depth=    1946 States=    9e+06 Transitions= 1.66e+07 Memory= 54235.520 t=     7.86 R=   1e+06
Depth=    1946 States=    1e+07 Transitions= 1.84e+07 Memory= 54313.352 t=     8.74 R=   1e+06
Depth=    1946 States=  1.1e+07 Transitions= 2.03e+07 Memory= 54391.965 t=     9.62 R=   1e+06
Depth=    1946 States=  1.2e+07 Transitions= 2.21e+07 Memory= 54469.895 t=     10.5 R=   1e+06
Depth=    1946 States=  1.3e+07 Transitions=  2.4e+07 Memory= 54547.629 t=     11.4 R=   1e+06
Depth=    1946 States=  1.4e+07 Transitions= 2.58e+07 Memory= 54625.461 t=     12.3 R=   1e+06
Depth=    1946 States=  1.5e+07 Transitions= 2.77e+07 Memory= 54702.610 t=     13.2 R=   1e+06
Depth=    1946 States=  1.6e+07 Transitions= 2.95e+07 Memory= 54780.051 t=     14.1 R=   1e+06
Depth=    1946 States=  1.7e+07 Transitions= 3.14e+07 Memory= 54857.981 t=     14.9 R=   1e+06
Depth=    1946 States=  1.8e+07 Transitions= 3.32e+07 Memory= 54935.227 t=     15.8 R=   1e+06
Depth=    1946 States=  1.9e+07 Transitions= 3.51e+07 Memory= 55012.570 t=     16.7 R=   1e+06
Depth=    1946 States=    2e+07 Transitions=  3.7e+07 Memory= 55090.403 t=     17.6 R=   1e+06
Depth=    1946 States=  2.1e+07 Transitions= 3.88e+07 Memory= 55167.844 t=     18.5 R=   1e+06
Depth=    1946 States=  2.2e+07 Transitions= 4.07e+07 Memory= 55245.188 t=     19.4 R=   1e+06
Depth=    1946 States=  2.3e+07 Transitions= 4.25e+07 Memory= 55323.117 t=     20.3 R=   1e+06
Depth=    1946 States=  2.4e+07 Transitions= 4.44e+07 Memory= 55401.242 t=     21.2 R=   1e+06
Depth=    1946 States=  2.5e+07 Transitions= 4.62e+07 Memory= 55479.074 t=     22.1 R=   1e+06
Depth=    1946 States=  2.6e+07 Transitions=  4.8e+07 Memory= 55557.004 t=     22.9 R=   1e+06
Depth=    1946 States=  2.7e+07 Transitions= 4.99e+07 Memory= 55634.934 t=     23.8 R=   1e+06
Depth=    1946 States=  2.8e+07 Transitions= 5.17e+07 Memory= 55712.961 t=     24.7 R=   1e+06
Depth=    1946 States=  2.9e+07 Transitions= 5.36e+07 Memory= 55790.598 t=     25.6 R=   1e+06
Depth=    1946 States=    3e+07 Transitions= 5.54e+07 Memory= 55868.528 t=     26.5 R=   1e+06
Depth=    1946 States=  3.1e+07 Transitions= 5.73e+07 Memory= 55946.653 t=     27.4 R=   1e+06
Depth=    1946 States=  3.2e+07 Transitions= 5.91e+07 Memory= 56024.289 t=     28.3 R=   1e+06
Depth=    1946 States=  3.3e+07 Transitions=  6.1e+07 Memory= 56102.219 t=     29.2 R=   1e+06
Depth=    1946 States=  3.4e+07 Transitions= 6.28e+07 Memory= 56179.953 t=     30.1 R=   1e+06
pan: resizing hashtable to -w26..  done
Depth=    1946 States=  3.5e+07 Transitions= 6.47e+07 Memory= 56754.063 t=     31.4 R=   1e+06
Depth=    1946 States=  3.6e+07 Transitions= 6.65e+07 Memory= 56831.992 t=     32.3 R=   1e+06
Depth=    1946 States=  3.7e+07 Transitions= 6.84e+07 Memory= 56910.020 t=     33.1 R=   1e+06
Depth=    1946 States=  3.8e+07 Transitions= 7.02e+07 Memory= 56987.754 t=       34 R=   1e+06
Depth=    1946 States=  3.9e+07 Transitions= 7.21e+07 Memory= 57065.488 t=     34.9 R=   1e+06
Depth=    1946 States=    4e+07 Transitions= 7.39e+07 Memory= 57143.223 t=     35.8 R=   1e+06
Depth=    1946 States=  4.1e+07 Transitions= 7.58e+07 Memory= 57220.664 t=     36.7 R=   1e+06
Depth=    1946 States=  4.2e+07 Transitions= 7.77e+07 Memory= 57298.301 t=     37.6 R=   1e+06
Depth=    1946 States=  4.3e+07 Transitions= 7.95e+07 Memory= 57376.426 t=     38.5 R=   1e+06
Depth=    1946 States=  4.4e+07 Transitions= 8.14e+07 Memory= 57453.574 t=     39.4 R=   1e+06
Depth=    1946 States=  4.5e+07 Transitions= 8.32e+07 Memory= 57530.820 t=     40.3 R=   1e+06
Depth=    1946 States=  4.6e+07 Transitions= 8.51e+07 Memory= 57608.360 t=     41.2 R=   1e+06
Depth=    1946 States=  4.7e+07 Transitions=  8.7e+07 Memory= 57685.606 t=     42.1 R=   1e+06
Depth=    1946 States=  4.8e+07 Transitions= 8.88e+07 Memory= 57763.242 t=       43 R=   1e+06
Depth=    1946 States=  4.9e+07 Transitions= 9.07e+07 Memory= 57841.270 t=     43.9 R=   1e+06
Depth=    1946 States=    5e+07 Transitions= 9.25e+07 Memory= 57919.199 t=     44.8 R=   1e+06
Depth=    1946 States=  5.1e+07 Transitions= 9.44e+07 Memory= 57997.715 t=     45.6 R=   1e+06
Depth=    1946 States=  5.2e+07 Transitions= 9.62e+07 Memory= 58075.938 t=     46.5 R=   1e+06
Depth=    1946 States=  5.3e+07 Transitions= 9.81e+07 Memory= 58153.770 t=     47.4 R=   1e+06
Depth=    1946 States=  5.4e+07 Transitions= 9.99e+07 Memory= 58231.797 t=     48.3 R=   1e+06
Depth=    1946 States=  5.5e+07 Transitions= 1.02e+08 Memory= 58309.238 t=     49.2 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (p0)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness enabled)
        invalid end states      - (disabled by never claim)

State-vector 492 byte, depth reached 1946, errors: 0
  9158283 states, stored (5.57989e+07 visited)
 47495629 states, matched
1.0329455e+08 transitions (= visited+matched)
 24422744 atomic steps
hash conflicts:   6909793 (resolved)

Stats on memory usage (in Megabytes):
 4541.690       equivalent memory usage for states (stored*(State-vector + overhead))
 4463.152       actual memory usage for states (compression: 98.27%)
                state-vector as stored = 483 byte + 28 byte overhead
  512.000       memory used for hash table (-w26)
53405.762       memory used for DFS stack (-m1000000000)
    9.468       memory lost to fragmentation
58371.445       total actual memory usage


unreached in proctype proc0
        fair_lock.pml:22, state 4, "lock_for_test.request!tid"
        fair_lock.pml:20, state 10, "(lock_for_test.is_locked)"
        fair_lock.pml:20, state 10, "(!(lock_for_test.is_locked))"
        fair_lock.pml:33, state 13, "(lock_for_test.flag[tid])"
        fair_lock.pml:75, state 19, "num_lock = (num_lock+1)"
        fair_lock.pml:76, state 20, "num_lock = (num_lock-1)"
        fair_lock.pml:57, state 23, "lock_for_test.request?p"
        fair_lock.pml:60, state 26, "lock_for_test.is_locked = 0"
        fair_lock.pml:56, state 27, "(lock_for_test.request?[p])"
        fair_lock.pml:56, state 27, "else"
        fair_lock.pml:55, state 30, "p = 0"
        fair_lock.pml:18, state 31, "need_wait = 0"
        fair_lock.pml:79, state 34, "-end-"
        (11 of 34 states)
unreached in proctype proc1
        fair_lock.pml:22, state 4, "lock_for_test.request!tid"
        fair_lock.pml:20, state 10, "(lock_for_test.is_locked)"
        fair_lock.pml:20, state 10, "(!(lock_for_test.is_locked))"
        fair_lock.pml:33, state 13, "(lock_for_test.flag[tid])"
        fair_lock.pml:18, state 18, "need_wait = 0"
        fair_lock.pml:84, state 19, "num_lock = (num_lock+1)"
        fair_lock.pml:85, state 20, "num_lock = (num_lock-1)"
        fair_lock.pml:57, state 23, "lock_for_test.request?p"
        fair_lock.pml:60, state 26, "lock_for_test.is_locked = 0"
        fair_lock.pml:56, state 27, "(lock_for_test.request?[p])"
        fair_lock.pml:56, state 27, "else"
        fair_lock.pml:55, state 30, "p = 0"
        fair_lock.pml:88, state 31, "is_fair = 1"
        fair_lock.pml:89, state 32, "-end-"
        (12 of 32 states)
unreached in proctype run_main
        fair_lock.pml:57, state 50, "lock_info[head].request?p"
        fair_lock.pml:60, state 53, "lock_info[head].is_locked = 0"
        fair_lock.pml:56, state 54, "(lock_info[head].request?[p])"
        fair_lock.pml:56, state 54, "else"
        fair_lock.pml:55, state 57, "p = 0"
        cooperative.pml:22, state 122, "lock_info[task].request!tid"
        cooperative.pml:20, state 128, "(lock_info[task].is_locked)"
        cooperative.pml:20, state 128, "(!(lock_info[task].is_locked))"
        cooperative.pml:33, state 131, "(lock_info[task].flag[tid])"
        cooperative.pml:49, state 138, "tasks[task].need_sched = 1"
        cooperative.pml:50, state 139, "printf('wake(): task = %d, state = %d\n',task,tasks[task].state)"
        cooperative.pml:57, state 142, "lock_info[task].request?p"
        cooperative.pml:60, state 145, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 146, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 146, "else"
        cooperative.pml:55, state 149, "p = 0"
        cooperative.pml:57, state 153, "lock_info[task].request?p"
        cooperative.pml:60, state 156, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 157, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 157, "else"
        cooperative.pml:55, state 160, "p = 0"
        cooperative.pml:54, state 162, "printf('wake(): task = %d, state = %d\n',task,tasks[task].state)"
        cooperative.pml:55, state 163, "tasks[task].state = Runnable"
        cooperative.pml:57, state 166, "lock_info[task].request?p"
        cooperative.pml:60, state 169, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 170, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 170, "else"
        cooperative.pml:55, state 173, "p = 0"
        cooperative.pml:22, state 177, "lock_scheduler.request!tid"
        cooperative.pml:20, state 183, "(lock_scheduler.is_locked)"
        cooperative.pml:20, state 183, "(!(lock_scheduler.is_locked))"
        cooperative.pml:33, state 186, "(lock_scheduler.flag[tid])"
        cooperative.pml:39, state 192, "queue!task"
        cooperative.pml:57, state 195, "lock_scheduler.request?p"
        cooperative.pml:60, state 198, "lock_scheduler.is_locked = 0"
        cooperative.pml:56, state 199, "(lock_scheduler.request?[p])"
        cooperative.pml:56, state 199, "else"
        cooperative.pml:55, state 202, "p = 0"
        cooperative.pml:18, state 203, "need_wait = 0"
        cooperative.pml:48, state 204, "(((tasks[task].state==Running)||(tasks[task].state==Runnable)))"
        cooperative.pml:48, state 204, "((tasks[task].state==Terminated))"
        cooperative.pml:48, state 204, "(((tasks[task].state==Waiting)||(tasks[task].state==Ready)))"
        cooperative.pml:18, state 206, "need_wait = 0"
        cooperative.pml:57, state 215, "lock_future[task].request?p"
        cooperative.pml:60, state 218, "lock_future[task].is_locked = 0"
        cooperative.pml:56, state 219, "(lock_future[task].request?[p])"
        cooperative.pml:56, state 219, "else"
        cooperative.pml:55, state 222, "p = 0"
        cooperative.pml:57, state 249, "lock_info[task].request?p"
        cooperative.pml:60, state 252, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 253, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 253, "else"
        cooperative.pml:55, state 256, "p = 0"
        cooperative.pml:57, state 259, "lock_future[task].request?p"
        cooperative.pml:60, state 262, "lock_future[task].is_locked = 0"
        cooperative.pml:56, state 263, "(lock_future[task].request?[p])"
        cooperative.pml:56, state 263, "else"
        cooperative.pml:55, state 266, "p = 0"
        cooperative.pml:57, state 318, "lock_info[(task-(4/2))].request?p"
        cooperative.pml:60, state 321, "lock_info[(task-(4/2))].is_locked = 0"
        cooperative.pml:56, state 322, "(lock_info[(task-(4/2))].request?[p])"
        cooperative.pml:56, state 322, "else"
        cooperative.pml:55, state 325, "p = 0"
        cooperative.pml:57, state 331, "lock_info[(task-(4/2))].request?p"
        cooperative.pml:57, state 412, "lock_info[(task+(4/2))].request?p"
        cooperative.pml:54, state 421, "printf('wake(): task = %d, state = %d\n',(task+(4/2)),tasks[(task+(4/2))].state)"
        cooperative.pml:55, state 422, "tasks[(task+(4/2))].state = Runnable"
        cooperative.pml:57, state 425, "lock_info[(task+(4/2))].request?p"
        cooperative.pml:60, state 428, "lock_info[(task+(4/2))].is_locked = 0"
        cooperative.pml:56, state 429, "(lock_info[(task+(4/2))].request?[p])"
        cooperative.pml:56, state 429, "else"
        cooperative.pml:55, state 432, "p = 0"
        cooperative.pml:22, state 436, "lock_scheduler.request!tid"
        cooperative.pml:20, state 442, "(lock_scheduler.is_locked)"
        cooperative.pml:20, state 442, "(!(lock_scheduler.is_locked))"
        cooperative.pml:33, state 445, "(lock_scheduler.flag[tid])"
        cooperative.pml:39, state 451, "queue!(task+(4/2))"
        cooperative.pml:57, state 454, "lock_scheduler.request?p"
        cooperative.pml:60, state 457, "lock_scheduler.is_locked = 0"
        cooperative.pml:56, state 458, "(lock_scheduler.request?[p])"
        cooperative.pml:56, state 458, "else"
        cooperative.pml:55, state 461, "p = 0"
        cooperative.pml:18, state 462, "need_wait = 0"
        cooperative.pml:57, state 475, "lock_future[task].request?p"
        cooperative.pml:57, state 514, "lock_info[task].request?p"
        cooperative.pml:218, state 581, "-end-"
        (70 of 581 states)
unreached in init
        fair_lock.pml:22, state 9, "lock_info[i].request!0"
        fair_lock.pml:33, state 18, "(lock_info[i].flag[0])"
        cooperative.pml:49, state 25, "tasks[i].need_sched = 1"
        cooperative.pml:50, state 26, "printf('wake(): task = %d, state = %d\n',i,tasks[i].state)"
        fair_lock.pml:57, state 29, "lock_info[i].request?p"
        fair_lock.pml:60, state 32, "lock_info[i].is_locked = 0"
        fair_lock.pml:56, state 33, "(lock_info[i].request?[p])"
        fair_lock.pml:56, state 33, "else"
        fair_lock.pml:55, state 36, "p = 0"
        fair_lock.pml:57, state 40, "lock_info[i].request?p"
        fair_lock.pml:60, state 43, "lock_info[i].is_locked = 0"
        fair_lock.pml:56, state 44, "(lock_info[i].request?[p])"
        fair_lock.pml:56, state 44, "else"
        fair_lock.pml:55, state 47, "p = 0"
        cooperative.pml:57, state 53, "lock_info[i].request?p"
        cooperative.pml:22, state 64, "lock_scheduler.request!0"
        cooperative.pml:33, state 73, "(lock_scheduler.flag[0])"
        cooperative.pml:57, state 82, "lock_scheduler.request?p"
        (16 of 109 states)
unreached in claim p0
        _spin_nvr.tmp:6, state 6, "-end-"
        (1 of 6 states)

pan: elapsed time 50 seconds
pan: rate   1116872 states/second
```

### Fairness (Subject 1 and 3)

```
spin -a cooperative.pml
ltl fairness: <> ((num_terminated==1))
gcc -O3 -o pan pan.c
./pan -f -a -m1000000000

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (fairness)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness enabled)
        invalid end states      - (disabled by never claim)

State-vector 448 byte, depth reached 370, errors: 0
     4054 states, stored (23357 visited)
    16677 states, matched
    40034 transitions (= visited+matched)
     9200 atomic steps
hash conflicts:         0 (resolved)

Stats on memory usage (in Megabytes):
    1.840       equivalent memory usage for states (stored*(State-vector + overhead))
    1.876       actual memory usage for states
  128.000       memory used for hash table (-w24)
53405.762       memory used for DFS stack (-m1000000000)
53535.617       total actual memory usage


unreached in proctype proc0
        fair_lock.pml:22, state 4, "lock_for_test.request!tid"
        fair_lock.pml:20, state 10, "(lock_for_test.is_locked)"
        fair_lock.pml:20, state 10, "(!(lock_for_test.is_locked))"
        fair_lock.pml:33, state 13, "(lock_for_test.flag[tid])"
        fair_lock.pml:75, state 19, "num_lock = (num_lock+1)"
        fair_lock.pml:76, state 20, "num_lock = (num_lock-1)"
        fair_lock.pml:57, state 23, "lock_for_test.request?p"
        fair_lock.pml:60, state 26, "lock_for_test.is_locked = 0"
        fair_lock.pml:56, state 27, "(lock_for_test.request?[p])"
        fair_lock.pml:56, state 27, "else"
        fair_lock.pml:55, state 30, "p = 0"
        fair_lock.pml:18, state 31, "need_wait = 0"
        fair_lock.pml:79, state 34, "-end-"
        (11 of 34 states)
unreached in proctype proc1
        fair_lock.pml:22, state 4, "lock_for_test.request!tid"
        fair_lock.pml:20, state 10, "(lock_for_test.is_locked)"
        fair_lock.pml:20, state 10, "(!(lock_for_test.is_locked))"
        fair_lock.pml:33, state 13, "(lock_for_test.flag[tid])"
        fair_lock.pml:18, state 18, "need_wait = 0"
        fair_lock.pml:84, state 19, "num_lock = (num_lock+1)"
        fair_lock.pml:85, state 20, "num_lock = (num_lock-1)"
        fair_lock.pml:57, state 23, "lock_for_test.request?p"
        fair_lock.pml:60, state 26, "lock_for_test.is_locked = 0"
        fair_lock.pml:56, state 27, "(lock_for_test.request?[p])"
        fair_lock.pml:56, state 27, "else"
        fair_lock.pml:55, state 30, "p = 0"
        fair_lock.pml:88, state 31, "is_fair = 1"
        fair_lock.pml:89, state 32, "-end-"
        (12 of 32 states)
unreached in proctype run_main
        fair_lock.pml:22, state 32, "lock_info[head].request!tid"
        fair_lock.pml:33, state 41, "(lock_info[head].flag[tid])"
        fair_lock.pml:57, state 50, "lock_info[head].request?p"
        fair_lock.pml:60, state 53, "lock_info[head].is_locked = 0"
        fair_lock.pml:56, state 54, "(lock_info[head].request?[p])"
        fair_lock.pml:56, state 54, "else"
        fair_lock.pml:55, state 57, "p = 0"
        cooperative.pml:57, state 67, "lock_info[head].request?p"
        cooperative.pml:57, state 89, "lock_scheduler.request?p"
        cooperative.pml:60, state 92, "lock_scheduler.is_locked = 0"
        cooperative.pml:56, state 93, "(lock_scheduler.request?[p])"
        cooperative.pml:56, state 93, "else"
        cooperative.pml:55, state 96, "p = 0"
        cooperative.pml:93, state 97, "result_next[tid] = -(1)"
        cooperative.pml:22, state 122, "lock_info[task].request!tid"
        cooperative.pml:20, state 128, "(lock_info[task].is_locked)"
        cooperative.pml:20, state 128, "(!(lock_info[task].is_locked))"
        cooperative.pml:33, state 131, "(lock_info[task].flag[tid])"
        cooperative.pml:52, state 138, "tasks[task].need_sched = 1"
        cooperative.pml:53, state 139, "printf('wake(): task = %d, state = %d\n',task,tasks[task].state)"
        cooperative.pml:57, state 142, "lock_info[task].request?p"
        cooperative.pml:60, state 145, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 146, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 146, "else"
        cooperative.pml:55, state 149, "p = 0"
        cooperative.pml:57, state 153, "lock_info[task].request?p"
        cooperative.pml:60, state 156, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 157, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 157, "else"
        cooperative.pml:55, state 160, "p = 0"
        cooperative.pml:57, state 162, "printf('wake(): task = %d, state = %d\n',task,tasks[task].state)"
        cooperative.pml:58, state 163, "tasks[task].state = Runnable"
        cooperative.pml:57, state 166, "lock_info[task].request?p"
        cooperative.pml:60, state 169, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 170, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 170, "else"
        cooperative.pml:55, state 173, "p = 0"
        cooperative.pml:22, state 177, "lock_scheduler.request!tid"
        cooperative.pml:20, state 183, "(lock_scheduler.is_locked)"
        cooperative.pml:20, state 183, "(!(lock_scheduler.is_locked))"
        cooperative.pml:33, state 186, "(lock_scheduler.flag[tid])"
        cooperative.pml:42, state 192, "queue!task"
        cooperative.pml:57, state 195, "lock_scheduler.request?p"
        cooperative.pml:60, state 198, "lock_scheduler.is_locked = 0"
        cooperative.pml:56, state 199, "(lock_scheduler.request?[p])"
        cooperative.pml:56, state 199, "else"
        cooperative.pml:55, state 202, "p = 0"
        cooperative.pml:18, state 203, "need_wait = 0"
        cooperative.pml:51, state 204, "(((tasks[task].state==Running)||(tasks[task].state==Runnable)))"
        cooperative.pml:51, state 204, "((tasks[task].state==Terminated))"
        cooperative.pml:51, state 204, "(((tasks[task].state==Waiting)||(tasks[task].state==Ready)))"
        cooperative.pml:18, state 206, "need_wait = 0"
        cooperative.pml:57, state 215, "lock_future[task].request?p"
        cooperative.pml:60, state 218, "lock_future[task].is_locked = 0"
        cooperative.pml:56, state 219, "(lock_future[task].request?[p])"
        cooperative.pml:56, state 219, "else"
        cooperative.pml:55, state 222, "p = 0"
        cooperative.pml:22, state 231, "lock_info[task].request!tid"
        cooperative.pml:33, state 240, "(lock_info[task].flag[tid])"
        cooperative.pml:57, state 249, "lock_info[task].request?p"
        cooperative.pml:60, state 252, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 253, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 253, "else"
        cooperative.pml:55, state 256, "p = 0"
        cooperative.pml:57, state 259, "lock_future[task].request?p"
        cooperative.pml:60, state 262, "lock_future[task].is_locked = 0"
        cooperative.pml:56, state 263, "(lock_future[task].request?[p])"
        cooperative.pml:56, state 263, "else"
        cooperative.pml:55, state 266, "p = 0"
        cooperative.pml:57, state 274, "lock_info[task].request?p"
        cooperative.pml:22, state 289, "lock_info[task].request!tid"
        cooperative.pml:20, state 295, "(lock_info[task].is_locked)"
        cooperative.pml:20, state 295, "(!(lock_info[task].is_locked))"
        cooperative.pml:33, state 298, "(lock_info[task].flag[tid])"
        cooperative.pml:52, state 305, "tasks[task].need_sched = 1"
        cooperative.pml:53, state 306, "printf('wake(): task = %d, state = %d\n',task,tasks[task].state)"
        cooperative.pml:57, state 309, "lock_info[task].request?p"
        cooperative.pml:60, state 312, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 313, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 313, "else"
        cooperative.pml:55, state 316, "p = 0"
        cooperative.pml:57, state 320, "lock_info[task].request?p"
        cooperative.pml:60, state 323, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 324, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 324, "else"
        cooperative.pml:55, state 327, "p = 0"
        cooperative.pml:57, state 329, "printf('wake(): task = %d, state = %d\n',task,tasks[task].state)"
        cooperative.pml:58, state 330, "tasks[task].state = Runnable"
        cooperative.pml:57, state 333, "lock_info[task].request?p"
        cooperative.pml:60, state 336, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 337, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 337, "else"
        cooperative.pml:55, state 340, "p = 0"
        cooperative.pml:22, state 344, "lock_scheduler.request!tid"
        cooperative.pml:20, state 350, "(lock_scheduler.is_locked)"
        cooperative.pml:20, state 350, "(!(lock_scheduler.is_locked))"
        cooperative.pml:33, state 353, "(lock_scheduler.flag[tid])"
        cooperative.pml:42, state 359, "queue!task"
        cooperative.pml:57, state 362, "lock_scheduler.request?p"
        cooperative.pml:60, state 365, "lock_scheduler.is_locked = 0"
        cooperative.pml:56, state 366, "(lock_scheduler.request?[p])"
        cooperative.pml:56, state 366, "else"
        cooperative.pml:55, state 369, "p = 0"
        cooperative.pml:18, state 370, "need_wait = 0"
        cooperative.pml:51, state 371, "(((tasks[task].state==Running)||(tasks[task].state==Runnable)))"
        cooperative.pml:51, state 371, "((tasks[task].state==Terminated))"
        cooperative.pml:51, state 371, "(((tasks[task].state==Waiting)||(tasks[task].state==Ready)))"
        cooperative.pml:18, state 373, "need_wait = 0"
        cooperative.pml:131, state 374, "result_future[tid] = Pending"
        cooperative.pml:57, state 380, "lock_future[task].request?p"
        cooperative.pml:199, state 407, "printf('Pending: tid = %d\n',tid)"
        cooperative.pml:206, state 413, "tasks[task].state = Waiting"
        cooperative.pml:208, state 414, "printf('Waiting: task = %d, state = %d\n',task,tasks[task].state)"
        cooperative.pml:212, state 416, "tasks[task].need_sched = 0"
        cooperative.pml:57, state 419, "lock_info[task].request?p"
        cooperative.pml:60, state 422, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 423, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 423, "else"
        cooperative.pml:55, state 426, "p = 0"
        cooperative.pml:22, state 430, "lock_scheduler.request!tid"
        cooperative.pml:20, state 436, "(lock_scheduler.is_locked)"
        cooperative.pml:20, state 436, "(!(lock_scheduler.is_locked))"
        cooperative.pml:33, state 439, "(lock_scheduler.flag[tid])"
        cooperative.pml:42, state 445, "queue!task"
        cooperative.pml:57, state 448, "lock_scheduler.request?p"
        cooperative.pml:60, state 451, "lock_scheduler.is_locked = 0"
        cooperative.pml:56, state 452, "(lock_scheduler.request?[p])"
        cooperative.pml:56, state 452, "else"
        cooperative.pml:55, state 455, "p = 0"
        cooperative.pml:18, state 456, "need_wait = 0"
        cooperative.pml:226, state 470, "tasks[task].is_terminated = 1"
        cooperative.pml:228, state 471, "printf('Terminated: task = %d, state = %d, num_terminated = %d,\n',task,tasks[task].state,num_terminated)"
        cooperative.pml:57, state 476, "lock_info[task].request?p"
        cooperative.pml:60, state 479, "lock_info[task].is_locked = 0"
        cooperative.pml:56, state 480, "(lock_info[task].request?[p])"
        cooperative.pml:56, state 480, "else"
        cooperative.pml:55, state 483, "p = 0"
        cooperative.pml:236, state 486, "-end-"
        (113 of 486 states)
unreached in init
        fair_lock.pml:22, state 9, "lock_info[i].request!0"
        fair_lock.pml:33, state 18, "(lock_info[i].flag[0])"
        cooperative.pml:52, state 25, "tasks[i].need_sched = 1"
        cooperative.pml:53, state 26, "printf('wake(): task = %d, state = %d\n',i,tasks[i].state)"
        fair_lock.pml:57, state 29, "lock_info[i].request?p"
        fair_lock.pml:60, state 32, "lock_info[i].is_locked = 0"
        fair_lock.pml:56, state 33, "(lock_info[i].request?[p])"
        fair_lock.pml:56, state 33, "else"
        fair_lock.pml:55, state 36, "p = 0"
        fair_lock.pml:57, state 40, "lock_info[i].request?p"
        fair_lock.pml:60, state 43, "lock_info[i].is_locked = 0"
        fair_lock.pml:56, state 44, "(lock_info[i].request?[p])"
        fair_lock.pml:56, state 44, "else"
        fair_lock.pml:55, state 47, "p = 0"
        cooperative.pml:57, state 53, "lock_info[i].request?p"
        cooperative.pml:22, state 64, "lock_scheduler.request!0"
        cooperative.pml:33, state 73, "(lock_scheduler.flag[0])"
        cooperative.pml:57, state 82, "lock_scheduler.request?p"
        (16 of 109 states)
unreached in claim fairness
        _spin_nvr.tmp:6, state 6, "-end-"
        (1 of 6 states)

pan: elapsed time 0.02 seconds
pan: rate   1167850 states/second
```
