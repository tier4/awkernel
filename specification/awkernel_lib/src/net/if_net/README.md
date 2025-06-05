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
Depth=     315 States=    1e+06 Transitions=  1.7e+06 Memory=   271.991 t=     0.84 R=   1e+06
Depth=     315 States=    2e+06 Transitions= 3.49e+06 Memory=   414.960 t=     1.72 R=   1e+06
Depth=     319 States=    3e+06 Transitions=  5.3e+06 Memory=   556.952 t=      2.6 R=   1e+06
Depth=     319 States=    4e+06 Transitions= 7.05e+06 Memory=   699.921 t=     3.47 R=   1e+06
Depth=     319 States=    5e+06 Transitions=  8.8e+06 Memory=   843.280 t=     4.34 R=   1e+06
Depth=     319 States=    6e+06 Transitions= 1.05e+07 Memory=   986.737 t=      5.2 R=   1e+06
Depth=     319 States=    7e+06 Transitions= 1.23e+07 Memory=  1129.706 t=      6.1 R=   1e+06
Depth=     319 States=    8e+06 Transitions= 1.41e+07 Memory=  1271.503 t=        7 R=   1e+06
Depth=     319 States=    9e+06 Transitions= 1.59e+07 Memory=  1414.765 t=      7.9 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (eventually_all_true)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 328 byte, depth reached 319, errors: 0
  4948159 states, stored (9.89632e+06 visited)
  7533532 states, matched
 17429848 transitions (= visited+matched)
 10965316 atomic steps
hash conflicts:   1124453 (resolved)

Stats on memory usage (in Megabytes):
 1679.940       equivalent memory usage for states (stored*(State-vector + overhead))
 1417.643       actual memory usage for states (compression: 84.39%)
                state-vector as stored = 272 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    0.534       memory used for DFS stack (-m10000)
    2.898       memory lost to fragmentation
 1543.280       total actual memory usage



pan: elapsed time 8.7 seconds
pan: rate 1137507.6 states/second
```
