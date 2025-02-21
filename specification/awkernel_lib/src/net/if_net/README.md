# Poll of if_net

## Target

- [awkernel_lib/src/net/if_net.rs](../../../../../awkernel_lib/src/net/if_net.rs).

## Subjects to be Verified

1. All IP packets will be transmitted eventually.

## Result

### Eventually Terminated

```text
spin -a if_net.pml
ltl eventually_all_true: (<> ((set[0]) && (set[1]))) && ([] ((! ((set[0]) && (set[1]))) || ([] ((set[0]) && (set[1])))))
gcc -O3 -o pan pan.c
rm -f *.trail
./pan -f -a -n
Depth=     248 States=    1e+06 Transitions= 1.85e+06 Memory=   173.749 t=     0.89 R=   1e+06
Depth=     248 States=    2e+06 Transitions= 3.76e+06 Memory=   217.011 t=     1.81 R=   1e+06
Depth=     249 States=    3e+06 Transitions=  5.7e+06 Memory=   259.980 t=     2.74 R=   1e+06
Depth=     249 States=    4e+06 Transitions= 7.61e+06 Memory=   303.534 t=     3.65 R=   1e+06
Depth=     249 States=    5e+06 Transitions= 9.53e+06 Memory=   346.796 t=     4.57 R=   1e+06
Depth=     249 States=    6e+06 Transitions= 1.14e+07 Memory=   388.983 t=     5.49 R=   1e+06
Depth=     249 States=    7e+06 Transitions= 1.34e+07 Memory=   433.124 t=     6.41 R=   1e+06
Depth=     249 States=    8e+06 Transitions= 1.54e+07 Memory=   475.312 t=     7.38 R=   1e+06
Depth=     249 States=    9e+06 Transitions= 1.74e+07 Memory=   519.062 t=     8.34 R=   1e+06
Depth=     249 States=    1e+07 Transitions= 1.95e+07 Memory=   559.491 t=     9.32 R=   1e+06
Depth=     249 States=  1.1e+07 Transitions= 2.16e+07 Memory=   601.874 t=     10.3 R=   1e+06
Depth=     249 States=  1.2e+07 Transitions= 2.37e+07 Memory=   643.573 t=     11.3 R=   1e+06
Depth=     249 States=  1.3e+07 Transitions= 2.57e+07 Memory=   686.151 t=     12.3 R=   1e+06
Depth=     249 States=  1.4e+07 Transitions= 2.79e+07 Memory=   726.581 t=     13.3 R=   1e+06
Depth=     249 States=  1.5e+07 Transitions= 2.99e+07 Memory=   768.183 t=     14.3 R=   1e+06
Depth=     249 States=  1.6e+07 Transitions= 3.21e+07 Memory=   808.026 t=     15.3 R=   1e+06
Depth=     249 States=  1.7e+07 Transitions= 3.43e+07 Memory=   822.480 t=     16.5 R=   1e+06
Depth=     249 States=  1.8e+07 Transitions= 3.62e+07 Memory=   866.230 t=     17.4 R=   1e+06
Depth=     249 States=  1.9e+07 Transitions= 3.81e+07 Memory=   908.026 t=     18.3 R=   1e+06
Depth=     249 States=    2e+07 Transitions= 4.01e+07 Memory=   952.069 t=     19.2 R=   1e+06
Depth=     249 States=  2.1e+07 Transitions=  4.2e+07 Memory=   995.429 t=     20.2 R=   1e+06
Depth=     249 States=  2.2e+07 Transitions= 4.39e+07 Memory=  1038.202 t=     21.1 R=   1e+06
Depth=     249 States=  2.3e+07 Transitions= 4.58e+07 Memory=  1081.073 t=       22 R=   1e+06
Depth=     249 States=  2.4e+07 Transitions= 4.77e+07 Memory=  1125.116 t=     22.9 R=   1e+06
Depth=     249 States=  2.5e+07 Transitions= 4.99e+07 Memory=  1166.815 t=     23.9 R=   1e+06
Depth=     249 States=  2.6e+07 Transitions=  5.2e+07 Memory=  1205.976 t=       25 R=   1e+06
Depth=     249 States=  2.7e+07 Transitions=  5.4e+07 Memory=  1249.237 t=     25.9 R=   1e+06
Depth=     249 States=  2.8e+07 Transitions= 5.62e+07 Memory=  1288.202 t=       27 R=   1e+06
Depth=     249 States=  2.9e+07 Transitions= 5.83e+07 Memory=  1330.585 t=       28 R=   1e+06
Depth=     249 States=    3e+07 Transitions= 6.03e+07 Memory=  1373.554 t=       29 R=   1e+06
Depth=     249 States=  3.1e+07 Transitions= 6.24e+07 Memory=  1416.913 t=       30 R=   1e+06
Depth=     249 States=  3.2e+07 Transitions= 6.44e+07 Memory=  1457.831 t=       31 R=   1e+06
Depth=     249 States=  3.3e+07 Transitions= 6.65e+07 Memory=  1499.237 t=       32 R=   1e+06
Depth=     249 States=  3.4e+07 Transitions= 6.87e+07 Memory=  1516.132 t=     33.1 R=   1e+06
pan: resizing hashtable to -w26..  done
Depth=     249 States=  3.5e+07 Transitions= 7.07e+07 Memory=  2055.476 t=     34.4 R=   1e+06
Depth=     249 States=  3.6e+07 Transitions= 7.27e+07 Memory=  2098.151 t=     35.4 R=   1e+06
Depth=     249 States=  3.7e+07 Transitions= 7.47e+07 Memory=  2140.144 t=     36.4 R=   1e+06
Depth=     249 States=  3.8e+07 Transitions= 7.68e+07 Memory=  2183.015 t=     37.3 R=   1e+06
Depth=     249 States=  3.9e+07 Transitions= 7.88e+07 Memory=  2225.983 t=     38.3 R=   1e+06
Depth=     249 States=    4e+07 Transitions=  8.1e+07 Memory=  2266.022 t=     39.3 R=   1e+06
Depth=     249 States=  4.1e+07 Transitions= 8.31e+07 Memory=  2307.429 t=     40.4 R=   1e+06
Depth=     249 States=  4.2e+07 Transitions= 8.51e+07 Memory=  2349.226 t=     41.3 R=   1e+06
Depth=     249 States=  4.3e+07 Transitions= 8.73e+07 Memory=  2387.995 t=     42.4 R=   1e+06
Depth=     249 States=  4.4e+07 Transitions= 8.94e+07 Memory=  2430.183 t=     43.4 R=   1e+06
Depth=     249 States=  4.5e+07 Transitions= 9.12e+07 Memory=  2474.519 t=     44.3 R=   1e+06
Depth=     249 States=  4.6e+07 Transitions= 9.31e+07 Memory=  2518.073 t=     45.2 R=   1e+06
Depth=     249 States=  4.7e+07 Transitions= 9.51e+07 Memory=  2560.847 t=     46.1 R=   1e+06
Depth=     249 States=  4.8e+07 Transitions=  9.7e+07 Memory=  2604.499 t=       47 R=   1e+06
Depth=     249 States=  4.9e+07 Transitions= 9.89e+07 Memory=  2647.663 t=     47.9 R=   1e+06
Depth=     249 States=    5e+07 Transitions= 1.01e+08 Memory=  2689.655 t=     48.9 R=   1e+06
Depth=     249 States=  5.1e+07 Transitions= 1.03e+08 Memory=  2705.280 t=     49.9 R=   1e+06
Depth=     249 States=  5.2e+07 Transitions= 1.05e+08 Memory=  2746.491 t=     50.9 R=   1e+06
Depth=     249 States=  5.3e+07 Transitions= 1.07e+08 Memory=  2789.167 t=     51.9 R=   1e+06
Depth=     249 States=  5.4e+07 Transitions= 1.09e+08 Memory=  2828.230 t=     52.9 R=   1e+06
Depth=     249 States=  5.5e+07 Transitions= 1.11e+08 Memory=  2870.710 t=     53.9 R=   1e+06
Depth=     249 States=  5.6e+07 Transitions= 1.13e+08 Memory=  2912.019 t=     54.9 R=   1e+06
Depth=     249 States=  5.7e+07 Transitions= 1.16e+08 Memory=  2953.913 t=     55.9 R=   1e+06
Depth=     249 States=  5.8e+07 Transitions= 1.18e+08 Memory=  2995.710 t=     56.9 R=   1e+06
Depth=     249 States=  5.9e+07 Transitions=  1.2e+08 Memory=  3037.800 t=     57.9 R=   1e+06
Depth=     249 States=    6e+07 Transitions= 1.22e+08 Memory=  3080.866 t=     58.8 R=   1e+06
Depth=     249 States=  6.1e+07 Transitions= 1.24e+08 Memory=  3123.054 t=     59.8 R=   1e+06
Depth=     249 States=  6.2e+07 Transitions= 1.26e+08 Memory=  3166.999 t=     60.7 R=   1e+06
Depth=     249 States=  6.3e+07 Transitions= 1.27e+08 Memory=  3209.480 t=     61.6 R=   1e+06
Depth=     249 States=  6.4e+07 Transitions= 1.29e+08 Memory=  3252.546 t=     62.5 R=   1e+06
Depth=     249 States=  6.5e+07 Transitions= 1.31e+08 Memory=  3295.417 t=     63.5 R=   1e+06
Depth=     249 States=  6.6e+07 Transitions= 1.33e+08 Memory=  3339.558 t=     64.4 R=   1e+06
Depth=     249 States=  6.7e+07 Transitions= 1.35e+08 Memory=  3381.940 t=     65.3 R=   1e+06
Depth=     261 States=  6.8e+07 Transitions= 1.37e+08 Memory=  3439.362 t=     66.4 R=   1e+06
Depth=     263 States=  6.9e+07 Transitions= 1.39e+08 Memory=  3765.046 t=     67.6 R=   1e+06
Depth=     263 States=    7e+07 Transitions= 1.41e+08 Memory=  4092.292 t=     68.9 R=   1e+06
Depth=     263 States=  7.1e+07 Transitions= 1.43e+08 Memory=  4418.073 t=     70.2 R=   1e+06
Depth=     263 States=  7.2e+07 Transitions= 1.45e+08 Memory=  4745.515 t=     71.5 R=   1e+06
Depth=     263 States=  7.3e+07 Transitions= 1.47e+08 Memory=  5071.687 t=     72.7 R=   1e+06
Depth=     263 States=  7.4e+07 Transitions= 1.49e+08 Memory=  5398.054 t=       74 R=   1e+06
Depth=     263 States=  7.5e+07 Transitions= 1.51e+08 Memory=  5724.030 t=     75.3 R=   1e+06
Depth=     263 States=  7.6e+07 Transitions= 1.53e+08 Memory=  6049.616 t=     76.6 R=   1e+06
Depth=     263 States=  7.7e+07 Transitions= 1.56e+08 Memory=  6378.230 t=     77.9 R=   1e+06
Depth=     263 States=  7.8e+07 Transitions= 1.58e+08 Memory=  6703.815 t=     79.3 R=   1e+06
Depth=     263 States=  7.9e+07 Transitions=  1.6e+08 Memory=  7031.159 t=     80.6 R=   1e+06
Depth=     263 States=    8e+07 Transitions= 1.62e+08 Memory=  7357.429 t=     81.9 R=   1e+06
Depth=     263 States=  8.1e+07 Transitions= 1.64e+08 Memory=  7684.089 t=     83.2 R=   1e+06
Depth=     263 States=  8.2e+07 Transitions= 1.66e+08 Memory=  8009.772 t=     84.5 R=   1e+06
Depth=     263 States=  8.3e+07 Transitions= 1.68e+08 Memory=  8335.358 t=     85.9 R=   1e+06
Depth=     263 States=  8.4e+07 Transitions=  1.7e+08 Memory=  8662.995 t=     87.2 R=   1e+06
Depth=     263 States=  8.5e+07 Transitions= 1.72e+08 Memory=  8989.265 t=     88.5 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (eventually_all_true)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness enabled)
        invalid end states      - (disabled by never claim)

State-vector 352 byte, depth reached 263, errors: 0
 26011603 states, stored (8.54809e+07 visited)
 87214875 states, matched
1.7269581e+08 transitions (= visited+matched)
2.1710157e+08 atomic steps
hash conflicts:   9732399 (resolved)

Stats on memory usage (in Megabytes):
 9426.507       equivalent memory usage for states (stored*(State-vector + overhead))
 8650.240       actual memory usage for states (compression: 91.77%)
                state-vector as stored = 321 byte + 28 byte overhead
  512.000       memory used for hash table (-w26)
    0.534       memory used for DFS stack (-m10000)
   15.405       memory lost to fragmentation
 9147.370       total actual memory usage



pan: elapsed time 89.1 seconds
pan: rate 959381.98 states/second
```
