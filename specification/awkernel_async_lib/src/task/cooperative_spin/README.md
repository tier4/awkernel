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

pan: elapsed time 0.02 seconds
pan: rate   1167850 states/second
```
