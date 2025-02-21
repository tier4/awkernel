# Poll of if_net

## Target

- [awkernel_lib/src/net/if_net.rs](../../../../../awkernel_lib/src/net/if_net.rs).

## Subjects to be Verified

1. All IP packets will be transmitted eventually.

## Result

### Eventually Terminated

```text
spin -a if_net.pml
ltl eventually_all_true: <> ([] ((set[0]) && (set[1])))
gcc -O3 -o pan pan.c
rm -f *.trail
./pan -a -n
Depth=     262 States=    1e+06 Transitions= 2.32e+06 Memory=   292.694 t=     1.18 R=   8e+05
Depth=     262 States=    2e+06 Transitions=  4.7e+06 Memory=   457.050 t=      2.4 R=   8e+05
Depth=     263 States=    3e+06 Transitions= 7.02e+06 Memory=   620.917 t=     3.59 R=   8e+05
Depth=     263 States=    4e+06 Transitions= 9.41e+06 Memory=   785.077 t=     4.82 R=   8e+05
Depth=     263 States=    5e+06 Transitions= 1.19e+07 Memory=   949.726 t=     6.08 R=   8e+05
Depth=     263 States=    6e+06 Transitions= 1.44e+07 Memory=  1114.276 t=     7.39 R=   8e+05
Depth=     263 States=    7e+06 Transitions=  1.7e+07 Memory=  1278.632 t=     8.71 R=   8e+05
Depth=     263 States=    8e+06 Transitions= 1.96e+07 Memory=  1440.644 t=     10.1 R=   8e+05
Depth=     263 States=    9e+06 Transitions= 2.23e+07 Memory=  1605.585 t=     11.4 R=   8e+05
Depth=     263 States=    1e+07 Transitions= 2.49e+07 Memory=  1770.233 t=     12.8 R=   8e+05
Depth=     263 States=  1.1e+07 Transitions= 2.74e+07 Memory=  1934.101 t=     14.1 R=   8e+05
Depth=     263 States=  1.2e+07 Transitions= 2.97e+07 Memory=  2098.749 t=     15.4 R=   8e+05
Depth=     263 States=  1.3e+07 Transitions= 3.21e+07 Memory=  2262.421 t=     16.6 R=   8e+05
Depth=     263 States=  1.4e+07 Transitions= 3.45e+07 Memory=  2426.874 t=     17.9 R=   8e+05
Depth=     263 States=  1.5e+07 Transitions= 3.69e+07 Memory=  2590.546 t=     19.2 R=   8e+05
Depth=     263 States=  1.6e+07 Transitions= 3.95e+07 Memory=  2754.804 t=     20.6 R=   8e+05
Depth=     263 States=  1.7e+07 Transitions= 4.21e+07 Memory=  2919.452 t=       22 R=   8e+05
Depth=     263 States=  1.8e+07 Transitions= 4.47e+07 Memory=  3084.198 t=     23.4 R=   8e+05
Depth=     263 States=  1.9e+07 Transitions= 4.73e+07 Memory=  3247.187 t=     24.8 R=   8e+05
Depth=     263 States=    2e+07 Transitions= 4.99e+07 Memory=  3412.030 t=     26.2 R=   8e+05
Depth=     263 States=  2.1e+07 Transitions= 5.25e+07 Memory=  3577.558 t=     27.6 R=   8e+05
Depth=     263 States=  2.2e+07 Transitions= 5.49e+07 Memory=  3742.304 t=     28.9 R=   8e+05
Depth=     263 States=  2.3e+07 Transitions= 5.76e+07 Memory=  3906.562 t=     30.4 R=   8e+05
Depth=     263 States=  2.4e+07 Transitions= 6.01e+07 Memory=  4069.550 t=     31.8 R=   8e+05
Depth=     263 States=  2.5e+07 Transitions= 6.27e+07 Memory=  4233.026 t=     33.2 R=   8e+05
Depth=     263 States=  2.6e+07 Transitions= 6.54e+07 Memory=  4397.675 t=     34.6 R=   8e+05
Depth=     263 States=  2.7e+07 Transitions=  6.8e+07 Memory=  4562.519 t=     36.1 R=   7e+05
Depth=     263 States=  2.8e+07 Transitions= 7.04e+07 Memory=  4727.460 t=     37.4 R=   7e+05
Depth=     263 States=  2.9e+07 Transitions= 7.28e+07 Memory=  4891.034 t=     38.8 R=   7e+05
Depth=     263 States=    3e+07 Transitions= 7.52e+07 Memory=  5054.901 t=     40.1 R=   7e+05
Depth=     263 States=  3.1e+07 Transitions= 7.75e+07 Memory=  5219.843 t=     41.4 R=   7e+05
Depth=     263 States=  3.2e+07 Transitions=    8e+07 Memory=  5382.929 t=     42.8 R=   7e+05
Depth=     263 States=  3.3e+07 Transitions= 8.26e+07 Memory=  5547.382 t=     44.3 R=   7e+05
Depth=     263 States=  3.4e+07 Transitions= 8.52e+07 Memory=  5711.933 t=     45.8 R=   7e+05
pan: resizing hashtable to -w26..  done
Depth=     263 States=  3.5e+07 Transitions= 8.79e+07 Memory=  6371.394 t=     48.1 R=   7e+05
Depth=     263 States=  3.6e+07 Transitions= 9.04e+07 Memory=  6534.480 t=     49.5 R=   7e+05
Depth=     263 States=  3.7e+07 Transitions= 9.31e+07 Memory=  6700.300 t=     50.8 R=   7e+05
Depth=     263 States=  3.8e+07 Transitions= 9.55e+07 Memory=  6864.753 t=     52.1 R=   7e+05
Depth=     263 States=  3.9e+07 Transitions= 9.79e+07 Memory=  7029.011 t=     53.4 R=   7e+05
Depth=     263 States=    4e+07 Transitions=    1e+08 Memory=  7193.659 t=     54.6 R=   7e+05
Depth=     263 States=  4.1e+07 Transitions= 1.03e+08 Memory=  7357.429 t=     55.9 R=   7e+05
Depth=     263 States=  4.2e+07 Transitions= 1.05e+08 Memory=  7522.663 t=     57.1 R=   7e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (eventually_all_true)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 352 byte, depth reached 263, errors: 0
 21003937 states, stored (4.20079e+07 visited)
 62962824 states, matched
1.049707e+08 transitions (= visited+matched)
1.1029631e+08 atomic steps
hash conflicts:  22020583 (resolved)

Stats on memory usage (in Megabytes):
 7611.748       equivalent memory usage for states (stored*(State-vector + overhead))
 7024.916       actual memory usage for states (compression: 92.29%)
                state-vector as stored = 323 byte + 28 byte overhead
  512.000       memory used for hash table (-w26)
    0.534       memory used for DFS stack (-m10000)
   13.519       memory lost to fragmentation
 7523.933       total actual memory usage



pan: elapsed time 57.1 seconds
pan: rate 735174.52 states/second
```
