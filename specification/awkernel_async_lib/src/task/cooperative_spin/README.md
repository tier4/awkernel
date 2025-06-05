# Cooperative Multitasking

SPIN version.

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
./pan -f -a -n
Depth=    1504 States=    1e+06 Transitions= 1.86e+06 Memory=   206.366 t=     0.88 R=   1e+06
Depth=    1526 States=    2e+06 Transitions= 3.73e+06 Memory=   283.808 t=     1.77 R=   1e+06
Depth=    1721 States=    3e+06 Transitions= 5.57e+06 Memory=   361.542 t=     2.64 R=   1e+06
Depth=    1721 States=    4e+06 Transitions=  7.4e+06 Memory=   439.374 t=     3.51 R=   1e+06
Depth=    1721 States=    5e+06 Transitions= 9.24e+06 Memory=   517.694 t=     4.39 R=   1e+06
Depth=    1721 States=    6e+06 Transitions= 1.11e+07 Memory=   596.112 t=     5.27 R=   1e+06
Depth=    1946 States=    7e+06 Transitions= 1.29e+07 Memory=   674.237 t=     6.16 R=   1e+06
Depth=    1946 States=    8e+06 Transitions= 1.47e+07 Memory=   752.460 t=     7.03 R=   1e+06
Depth=    1946 States=    9e+06 Transitions= 1.66e+07 Memory=   830.292 t=     7.91 R=   1e+06
Depth=    1946 States=    1e+07 Transitions= 1.84e+07 Memory=   908.124 t=     8.79 R=   1e+06
Depth=    1946 States=  1.1e+07 Transitions= 2.03e+07 Memory=   986.737 t=     9.68 R=   1e+06
Depth=    1946 States=  1.2e+07 Transitions= 2.21e+07 Memory=  1064.667 t=     10.6 R=   1e+06
Depth=    1946 States=  1.3e+07 Transitions=  2.4e+07 Memory=  1142.401 t=     11.5 R=   1e+06
Depth=    1946 States=  1.4e+07 Transitions= 2.58e+07 Memory=  1220.233 t=     12.4 R=   1e+06
Depth=    1946 States=  1.5e+07 Transitions= 2.77e+07 Memory=  1297.382 t=     13.3 R=   1e+06
Depth=    1946 States=  1.6e+07 Transitions= 2.95e+07 Memory=  1374.823 t=     14.2 R=   1e+06
Depth=    1946 States=  1.7e+07 Transitions= 3.14e+07 Memory=  1452.753 t=       15 R=   1e+06
Depth=    1946 States=  1.8e+07 Transitions= 3.32e+07 Memory=  1529.999 t=     15.9 R=   1e+06
Depth=    1946 States=  1.9e+07 Transitions= 3.51e+07 Memory=  1607.343 t=     16.9 R=   1e+06
Depth=    1946 States=    2e+07 Transitions=  3.7e+07 Memory=  1685.175 t=     17.7 R=   1e+06
Depth=    1946 States=  2.1e+07 Transitions= 3.88e+07 Memory=  1762.616 t=     18.6 R=   1e+06
Depth=    1946 States=  2.2e+07 Transitions= 4.07e+07 Memory=  1839.960 t=     19.5 R=   1e+06
Depth=    1946 States=  2.3e+07 Transitions= 4.25e+07 Memory=  1917.890 t=     20.4 R=   1e+06
Depth=    1946 States=  2.4e+07 Transitions= 4.44e+07 Memory=  1996.015 t=     21.3 R=   1e+06
Depth=    1946 States=  2.5e+07 Transitions= 4.62e+07 Memory=  2073.847 t=     22.2 R=   1e+06
Depth=    1946 States=  2.6e+07 Transitions=  4.8e+07 Memory=  2151.776 t=     23.1 R=   1e+06
Depth=    1946 States=  2.7e+07 Transitions= 4.99e+07 Memory=  2229.706 t=       24 R=   1e+06
Depth=    1946 States=  2.8e+07 Transitions= 5.17e+07 Memory=  2307.733 t=     24.9 R=   1e+06
Depth=    1946 States=  2.9e+07 Transitions= 5.36e+07 Memory=  2385.370 t=     25.8 R=   1e+06
Depth=    1946 States=    3e+07 Transitions= 5.54e+07 Memory=  2463.300 t=     26.7 R=   1e+06
Depth=    1946 States=  3.1e+07 Transitions= 5.73e+07 Memory=  2541.425 t=     27.6 R=   1e+06
Depth=    1946 States=  3.2e+07 Transitions= 5.91e+07 Memory=  2619.062 t=     28.5 R=   1e+06
Depth=    1946 States=  3.3e+07 Transitions=  6.1e+07 Memory=  2696.991 t=     29.4 R=   1e+06
Depth=    1946 States=  3.4e+07 Transitions= 6.28e+07 Memory=  2774.726 t=     30.3 R=   1e+06
pan: resizing hashtable to -w26..  done
Depth=    1946 States=  3.5e+07 Transitions= 6.47e+07 Memory=  3348.835 t=     31.6 R=   1e+06
Depth=    1946 States=  3.6e+07 Transitions= 6.65e+07 Memory=  3426.765 t=     32.5 R=   1e+06
Depth=    1946 States=  3.7e+07 Transitions= 6.84e+07 Memory=  3504.792 t=     33.4 R=   1e+06
Depth=    1946 States=  3.8e+07 Transitions= 7.02e+07 Memory=  3582.526 t=     34.3 R=   1e+06
Depth=    1946 States=  3.9e+07 Transitions= 7.21e+07 Memory=  3660.261 t=     35.2 R=   1e+06
Depth=    1946 States=    4e+07 Transitions= 7.39e+07 Memory=  3737.995 t=     36.1 R=   1e+06
Depth=    1946 States=  4.1e+07 Transitions= 7.58e+07 Memory=  3815.437 t=       37 R=   1e+06
Depth=    1946 States=  4.2e+07 Transitions= 7.77e+07 Memory=  3893.073 t=     37.9 R=   1e+06
Depth=    1946 States=  4.3e+07 Transitions= 7.95e+07 Memory=  3971.198 t=     38.7 R=   1e+06
Depth=    1946 States=  4.4e+07 Transitions= 8.14e+07 Memory=  4048.347 t=     39.6 R=   1e+06
Depth=    1946 States=  4.5e+07 Transitions= 8.32e+07 Memory=  4125.593 t=     40.5 R=   1e+06
Depth=    1946 States=  4.6e+07 Transitions= 8.51e+07 Memory=  4203.132 t=     41.4 R=   1e+06
Depth=    1946 States=  4.7e+07 Transitions=  8.7e+07 Memory=  4280.378 t=     42.3 R=   1e+06
Depth=    1946 States=  4.8e+07 Transitions= 8.88e+07 Memory=  4358.015 t=     43.2 R=   1e+06
Depth=    1946 States=  4.9e+07 Transitions= 9.07e+07 Memory=  4436.042 t=     44.1 R=   1e+06
Depth=    1946 States=    5e+07 Transitions= 9.25e+07 Memory=  4513.972 t=       45 R=   1e+06
Depth=    1946 States=  5.1e+07 Transitions= 9.44e+07 Memory=  4592.487 t=     45.9 R=   1e+06
Depth=    1946 States=  5.2e+07 Transitions= 9.62e+07 Memory=  4670.710 t=     46.8 R=   1e+06
Depth=    1946 States=  5.3e+07 Transitions= 9.81e+07 Memory=  4748.542 t=     47.7 R=   1e+06
Depth=    1946 States=  5.4e+07 Transitions= 9.99e+07 Memory=  4826.569 t=     48.6 R=   1e+06
Depth=    1946 States=  5.5e+07 Transitions= 1.02e+08 Memory=  4904.011 t=     49.5 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (eventually_terminate)
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
    0.534       memory used for DFS stack (-m10000)
    9.468       memory lost to fragmentation
 4966.218       total actual memory usage



pan: elapsed time 50.3 seconds
pan: rate 1110205.4 states/second
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
    0.534       memory used for DFS stack (-m10000)
  130.390       total actual memory usage



pan: elapsed time 0.02 seconds
pan: rate   1167850 states/second
```
