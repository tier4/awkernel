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
Depth=     495 States=    1e+06 Transitions= 1.62e+06 Memory=   155.878	t=     0.67 R=   1e+06
Depth=     547 States=    2e+06 Transitions=  3.3e+06 Memory=   193.183	t=     1.39 R=   1e+06
Depth=     547 States=    3e+06 Transitions= 5.02e+06 Memory=   209.198	t=     2.13 R=   1e+06
Depth=     653 States=    4e+06 Transitions= 6.72e+06 Memory=   250.409	t=     2.85 R=   1e+06
Depth=     653 States=    5e+06 Transitions= 8.43e+06 Memory=   262.616	t=     3.59 R=   1e+06
Depth=     653 States=    6e+06 Transitions= 1.03e+07 Memory=   289.374	t=     4.34 R=   1e+06
Depth=     659 States=    7e+06 Transitions= 1.23e+07 Memory=   315.839	t=     5.13 R=   1e+06
Depth=     659 States=    8e+06 Transitions= 1.41e+07 Memory=   344.062	t=     5.91 R=   1e+06
Depth=     659 States=    9e+06 Transitions= 1.59e+07 Memory=   373.554	t=     6.71 R=   1e+06
Depth=     673 States=    1e+07 Transitions= 1.77e+07 Memory=   397.968	t=      7.5 R=   1e+06
Depth=     673 States=  1.1e+07 Transitions= 1.95e+07 Memory=   422.772	t=      8.3 R=   1e+06
Depth=     673 States=  1.2e+07 Transitions= 2.15e+07 Memory=   449.530	t=     9.13 R=   1e+06
Depth=     673 States=  1.3e+07 Transitions= 2.34e+07 Memory=   476.190	t=     9.96 R=   1e+06
Depth=     673 States=  1.4e+07 Transitions= 2.54e+07 Memory=   503.046	t=     10.8 R=   1e+06
Depth=     673 States=  1.5e+07 Transitions= 2.73e+07 Memory=   529.608	t=     11.6 R=   1e+06
Depth=     673 States=  1.6e+07 Transitions= 2.92e+07 Memory=   557.636	t=     12.4 R=   1e+06
Depth=     677 States=  1.7e+07 Transitions= 3.11e+07 Memory=   583.026	t=     13.2 R=   1e+06
Depth=     677 States=  1.8e+07 Transitions= 3.33e+07 Memory=   609.687	t=     14.1 R=   1e+06
Depth=     677 States=  1.9e+07 Transitions= 3.53e+07 Memory=   636.444	t=     14.9 R=   1e+06
Depth=     677 States=    2e+07 Transitions= 3.75e+07 Memory=   663.300	t=     15.8 R=   1e+06
Depth=     677 States=  2.1e+07 Transitions= 3.98e+07 Memory=   689.862	t=     16.8 R=   1e+06
Depth=     677 States=  2.2e+07 Transitions= 4.16e+07 Memory=   724.726	t=     17.7 R=   1e+06
Depth=     677 States=  2.3e+07 Transitions= 4.33e+07 Memory=   748.261	t=     18.5 R=   1e+06
Depth=     677 States=  2.4e+07 Transitions=  4.5e+07 Memory=   771.210	t=     19.4 R=   1e+06
Depth=     677 States=  2.5e+07 Transitions= 4.66e+07 Memory=   808.417	t=     20.2 R=   1e+06
Depth=     677 States=  2.6e+07 Transitions= 4.84e+07 Memory=   823.749	t=       21 R=   1e+06
Depth=     677 States=  2.7e+07 Transitions= 5.02e+07 Memory=   850.214	t=     21.9 R=   1e+06
Depth=     677 States=  2.8e+07 Transitions= 5.22e+07 Memory=   876.972	t=     22.8 R=   1e+06
Depth=     677 States=  2.9e+07 Transitions=  5.4e+07 Memory=   903.730	t=     23.7 R=   1e+06
Depth=     677 States=    3e+07 Transitions= 5.59e+07 Memory=   930.390	t=     24.6 R=   1e+06
Depth=     677 States=  3.1e+07 Transitions= 5.77e+07 Memory=   957.245	t=     25.5 R=   1e+06
Depth=     677 States=  3.2e+07 Transitions= 5.95e+07 Memory=   984.687	t=     26.4 R=   1e+06
Depth=     677 States=  3.3e+07 Transitions= 6.14e+07 Memory=  1010.468	t=     27.3 R=   1e+06
Depth=     677 States=  3.4e+07 Transitions= 6.33e+07 Memory=  1037.421	t=     28.2 R=   1e+06
pan: resizing hashtable to -w26..  done
Depth=     677 States=  3.5e+07 Transitions= 6.53e+07 Memory=  1560.261	t=     29.9 R=   1e+06
Depth=     677 States=  3.6e+07 Transitions= 6.72e+07 Memory=  1586.921	t=     30.7 R=   1e+06
Depth=     677 States=  3.7e+07 Transitions= 6.91e+07 Memory=  1613.776	t=     31.5 R=   1e+06
Depth=     677 States=  3.8e+07 Transitions= 7.11e+07 Memory=  1640.534	t=     32.4 R=   1e+06
Depth=     677 States=  3.9e+07 Transitions= 7.32e+07 Memory=  1667.292	t=     33.2 R=   1e+06
Depth=     677 States=    4e+07 Transitions= 7.52e+07 Memory=  1694.050	t=     34.1 R=   1e+06
Depth=     677 States=  4.1e+07 Transitions= 7.74e+07 Memory=  1720.222	t=       35 R=   1e+06
Depth=     677 States=  4.2e+07 Transitions= 7.97e+07 Memory=  1746.980	t=     35.9 R=   1e+06
Depth=     677 States=  4.3e+07 Transitions= 8.18e+07 Memory=  1773.933	t=     36.8 R=   1e+06
Depth=     677 States=  4.4e+07 Transitions= 8.38e+07 Memory=  1800.397	t=     37.7 R=   1e+06
Depth=     677 States=  4.5e+07 Transitions= 8.57e+07 Memory=  1827.058	t=     38.6 R=   1e+06
Depth=     677 States=  4.6e+07 Transitions= 8.77e+07 Memory=  1853.815	t=     39.5 R=   1e+06
Depth=     677 States=  4.7e+07 Transitions= 8.96e+07 Memory=  1880.476	t=     40.4 R=   1e+06
Depth=     677 States=  4.8e+07 Transitions= 9.17e+07 Memory=  1907.233	t=     41.2 R=   1e+06
Depth=     699 States=  4.9e+07 Transitions= 9.36e+07 Memory=  1933.894	t=     42.1 R=   1e+06
Depth=     699 States=    5e+07 Transitions= 9.56e+07 Memory=  1961.140	t=       43 R=   1e+06
Depth=     699 States=  5.1e+07 Transitions= 9.76e+07 Memory=  1987.507	t=     43.8 R=   1e+06
Depth=     699 States=  5.2e+07 Transitions= 9.96e+07 Memory=  2014.069	t=     44.7 R=   1e+06
Depth=     699 States=  5.3e+07 Transitions= 1.02e+08 Memory=  2040.827	t=     45.6 R=   1e+06
Depth=     699 States=  5.4e+07 Transitions= 1.04e+08 Memory=  2067.683	t=     46.5 R=   1e+06
Depth=     699 States=  5.5e+07 Transitions= 1.06e+08 Memory=  2095.417	t=     47.4 R=   1e+06
Depth=     699 States=  5.6e+07 Transitions= 1.08e+08 Memory=  2121.784	t=     48.3 R=   1e+06
Depth=     699 States=  5.7e+07 Transitions=  1.1e+08 Memory=  2147.956	t=     49.2 R=   1e+06
Depth=     699 States=  5.8e+07 Transitions= 1.12e+08 Memory=  2174.714	t=       50 R=   1e+06
Depth=     699 States=  5.9e+07 Transitions= 1.14e+08 Memory=  2201.374	t=     50.9 R=   1e+06
Depth=     699 States=    6e+07 Transitions= 1.16e+08 Memory=  2228.230	t=     51.8 R=   1e+06
Depth=     699 States=  6.1e+07 Transitions= 1.18e+08 Memory=  2254.987	t=     52.7 R=   1e+06
Depth=     699 States=  6.2e+07 Transitions=  1.2e+08 Memory=  2281.257	t=     53.7 R=   1e+06
Depth=     699 States=  6.3e+07 Transitions= 1.22e+08 Memory=  2307.917	t=     54.6 R=   1e+06
Depth=     699 States=  6.4e+07 Transitions= 1.24e+08 Memory=  2334.577	t=     55.5 R=   1e+06
Depth=     699 States=  6.5e+07 Transitions= 1.26e+08 Memory=  2361.335	t=     56.4 R=   1e+06
Depth=     699 States=  6.6e+07 Transitions= 1.29e+08 Memory=  2388.581	t=     57.4 R=   1e+06
Depth=     699 States=  6.7e+07 Transitions= 1.31e+08 Memory=  2415.241	t=     58.4 R=   1e+06
Depth=     699 States=  6.8e+07 Transitions= 1.34e+08 Memory=  2441.901	t=     59.4 R=   1e+06
Depth=     699 States=  6.9e+07 Transitions= 1.36e+08 Memory=  2468.269	t=     60.4 R=   1e+06
Depth=     699 States=    7e+07 Transitions= 1.38e+08 Memory=  2495.319	t=     61.3 R=   1e+06
Depth=     699 States=  7.1e+07 Transitions=  1.4e+08 Memory=  2521.589	t=     62.2 R=   1e+06
Depth=     699 States=  7.2e+07 Transitions= 1.42e+08 Memory=  2548.444	t=     63.2 R=   1e+06
Depth=     699 States=  7.3e+07 Transitions= 1.44e+08 Memory=  2575.593	t=     64.2 R=   1e+06
Depth=     699 States=  7.4e+07 Transitions= 1.47e+08 Memory=  2603.132	t=     65.3 R=   1e+06
Depth=     699 States=  7.5e+07 Transitions= 1.49e+08 Memory=  2628.522	t=     66.3 R=   1e+06
Depth=     709 States=  7.6e+07 Transitions= 1.52e+08 Memory=  2655.280	t=     67.2 R=   1e+06
Depth=     737 States=  7.7e+07 Transitions= 1.54e+08 Memory=  2682.722	t=     68.2 R=   1e+06
Depth=     803 States=  7.8e+07 Transitions= 1.56e+08 Memory=  2709.870	t=     69.2 R=   1e+06
Depth=     803 States=  7.9e+07 Transitions= 1.59e+08 Memory=  2735.847	t=     70.2 R=   1e+06
Depth=     803 States=    8e+07 Transitions= 1.61e+08 Memory=  2762.116	t=     71.2 R=   1e+06
Depth=     803 States=  8.1e+07 Transitions= 1.63e+08 Memory=  2788.874	t=     72.2 R=   1e+06
Depth=     803 States=  8.2e+07 Transitions= 1.66e+08 Memory=  2815.632	t=     73.2 R=   1e+06
Depth=     803 States=  8.3e+07 Transitions= 1.68e+08 Memory=  2842.976	t=     74.3 R=   1e+06
Depth=     803 States=  8.4e+07 Transitions= 1.71e+08 Memory=  2869.147	t=     75.3 R=   1e+06
Depth=     803 States=  8.5e+07 Transitions= 1.73e+08 Memory=  2896.296	t=     76.3 R=   1e+06
Depth=     803 States=  8.6e+07 Transitions= 1.75e+08 Memory=  2922.468	t=     77.3 R=   1e+06
Depth=     803 States=  8.7e+07 Transitions= 1.78e+08 Memory=  2949.128	t=     78.3 R=   1e+06
Depth=     803 States=  8.8e+07 Transitions=  1.8e+08 Memory=  2976.081	t=     79.4 R=   1e+06
Depth=     803 States=  8.9e+07 Transitions= 1.83e+08 Memory=  3002.546	t=     80.4 R=   1e+06
Depth=     803 States=    9e+07 Transitions= 1.85e+08 Memory=  3029.401	t=     81.5 R=   1e+06
Depth=     803 States=  9.1e+07 Transitions= 1.88e+08 Memory=  3055.964	t=     82.5 R=   1e+06
Depth=     803 States=  9.2e+07 Transitions= 1.91e+08 Memory=  3082.722	t=     83.6 R=   1e+06
Depth=     803 States=  9.3e+07 Transitions= 1.93e+08 Memory=  3109.480	t=     84.7 R=   1e+06
Depth=     803 States=  9.4e+07 Transitions= 1.96e+08 Memory=  3136.628	t=     85.8 R=   1e+06
Depth=     823 States=  9.5e+07 Transitions= 1.98e+08 Memory=  3162.995	t=     86.9 R=   1e+06
Depth=     847 States=  9.6e+07 Transitions= 2.01e+08 Memory=  3189.655	t=       88 R=   1e+06
Depth=     847 States=  9.7e+07 Transitions= 2.04e+08 Memory=  3216.413	t=     89.1 R=   1e+06
Depth=     847 States=  9.8e+07 Transitions= 2.06e+08 Memory=  3242.976	t=     90.2 R=   1e+06
Depth=     847 States=  9.9e+07 Transitions= 2.08e+08 Memory=  3270.319	t=     91.2 R=   1e+06
Depth=     847 States=    1e+08 Transitions= 2.11e+08 Memory=  3296.394	t=     92.3 R=   1e+06
Depth=     847 States= 1.01e+08 Transitions= 2.14e+08 Memory=  3323.151	t=     93.3 R=   1e+06
Depth=     847 States= 1.02e+08 Transitions= 2.16e+08 Memory=  3349.909	t=     94.5 R=   1e+06
Depth=     847 States= 1.03e+08 Transitions= 2.19e+08 Memory=  3376.569	t=     95.6 R=   1e+06
Depth=     847 States= 1.04e+08 Transitions= 2.21e+08 Memory=  3403.522	t=     96.7 R=   1e+06
Depth=     847 States= 1.05e+08 Transitions= 2.24e+08 Memory=  3430.085	t=     97.8 R=   1e+06
Depth=     847 States= 1.06e+08 Transitions= 2.27e+08 Memory=  3456.940	t=       99 R=   1e+06
Depth=     847 States= 1.07e+08 Transitions= 2.29e+08 Memory=  3483.503	t=      100 R=   1e+06
Depth=     847 States= 1.08e+08 Transitions= 2.32e+08 Memory=  3510.163	t=      101 R=   1e+06
Depth=     847 States= 1.09e+08 Transitions= 2.34e+08 Memory=  3536.921	t=      102 R=   1e+06
Depth=     847 States=  1.1e+08 Transitions= 2.37e+08 Memory=  3563.581	t=      103 R=   1e+06
Depth=     847 States= 1.11e+08 Transitions= 2.39e+08 Memory=  3590.241	t=      105 R=   1e+06
Depth=     847 States= 1.12e+08 Transitions= 2.42e+08 Memory=  3616.999	t=      106 R=   1e+06
Depth=     847 States= 1.13e+08 Transitions= 2.45e+08 Memory=  3643.757	t=      107 R=   1e+06
Depth=     847 States= 1.14e+08 Transitions= 2.47e+08 Memory=  3670.515	t=      108 R=   1e+06
Depth=     847 States= 1.15e+08 Transitions=  2.5e+08 Memory=  3697.370	t=      109 R=   1e+06
Depth=     847 States= 1.16e+08 Transitions= 2.52e+08 Memory=  3724.128	t=      110 R=   1e+06
Depth=     847 States= 1.17e+08 Transitions= 2.55e+08 Memory=  3750.886	t=      111 R=   1e+06
Depth=     847 States= 1.18e+08 Transitions= 2.57e+08 Memory=  3777.644	t=      112 R=   1e+06
Depth=     847 States= 1.19e+08 Transitions=  2.6e+08 Memory=  3804.401	t=      113 R=   1e+06
Depth=     847 States=  1.2e+08 Transitions= 2.63e+08 Memory=  3830.964	t=      114 R=   1e+06
Depth=     847 States= 1.21e+08 Transitions= 2.65e+08 Memory=  3857.819	t=      115 R=   1e+06
Depth=     847 States= 1.22e+08 Transitions= 2.68e+08 Memory=  3884.675	t=      117 R=   1e+06
Depth=     847 States= 1.23e+08 Transitions=  2.7e+08 Memory=  3911.433	t=      118 R=   1e+06
Depth=     847 States= 1.24e+08 Transitions= 2.73e+08 Memory=  3938.093	t=      119 R=   1e+06
Depth=     847 States= 1.25e+08 Transitions= 2.75e+08 Memory=  3964.851	t=      120 R=   1e+06
Depth=     847 States= 1.26e+08 Transitions= 2.78e+08 Memory=  3991.120	t=      121 R=   1e+06
Depth=     847 States= 1.27e+08 Transitions=  2.8e+08 Memory=  4017.683	t=      122 R=   1e+06
Depth=     847 States= 1.28e+08 Transitions= 2.83e+08 Memory=  4044.440	t=      123 R=   1e+06
Depth=     847 States= 1.29e+08 Transitions= 2.85e+08 Memory=  4078.913	t=      124 R=   1e+06
Depth=     847 States=  1.3e+08 Transitions= 2.86e+08 Memory=  4103.425	t=      125 R=   1e+06
Depth=     847 States= 1.31e+08 Transitions= 2.88e+08 Memory=  4125.397	t=      126 R=   1e+06
Depth=     847 States= 1.32e+08 Transitions=  2.9e+08 Memory=  4163.581	t=      127 R=   1e+06
Depth=     847 States= 1.33e+08 Transitions= 2.91e+08 Memory=  4178.034	t=      128 R=   1e+06
Depth=     847 States= 1.34e+08 Transitions= 2.93e+08 Memory=  4205.183	t=      129 R=   1e+06
Depth=     847 States= 1.35e+08 Transitions= 2.95e+08 Memory=  4231.550	t=      130 R=   1e+06
pan: resizing hashtable to -w28..  done
Depth=     847 States= 1.36e+08 Transitions= 2.97e+08 Memory=  6279.550	t=      135 R=   1e+06
Depth=     847 States= 1.37e+08 Transitions= 2.99e+08 Memory=  6279.550	t=      136 R=   1e+06
Depth=     847 States= 1.38e+08 Transitions= 3.01e+08 Memory=  6299.765	t=      137 R=   1e+06
Depth=     847 States= 1.39e+08 Transitions= 3.03e+08 Memory=  6322.421	t=      138 R=   1e+06
Depth=     847 States=  1.4e+08 Transitions= 3.04e+08 Memory=  6349.179	t=      138 R=   1e+06
Depth=     847 States= 1.41e+08 Transitions= 3.06e+08 Memory=  6376.815	t=      139 R=   1e+06
Depth=     847 States= 1.42e+08 Transitions= 3.08e+08 Memory=  6402.792	t=      140 R=   1e+06
Depth=     847 States= 1.43e+08 Transitions=  3.1e+08 Memory=  6429.550	t=      141 R=   1e+06
Depth=     847 States= 1.44e+08 Transitions= 3.12e+08 Memory=  6456.308	t=      142 R=   1e+06
Depth=     847 States= 1.45e+08 Transitions= 3.14e+08 Memory=  6483.065	t=      143 R=   1e+06
Depth=     847 States= 1.46e+08 Transitions= 3.16e+08 Memory=  6510.019	t=      144 R=   1e+06
Depth=     847 States= 1.47e+08 Transitions= 3.18e+08 Memory=  6536.679	t=      145 R=   1e+06
Depth=     847 States= 1.48e+08 Transitions= 3.21e+08 Memory=  6563.437	t=      146 R=   1e+06
Depth=     847 States= 1.49e+08 Transitions= 3.23e+08 Memory=  6589.706	t=      147 R=   1e+06
Depth=     847 States=  1.5e+08 Transitions= 3.25e+08 Memory=  6617.538	t=      148 R=   1e+06
Depth=     847 States= 1.51e+08 Transitions= 3.27e+08 Memory=  6643.124	t=      149 R=   1e+06
Depth=     847 States= 1.52e+08 Transitions= 3.29e+08 Memory=  6669.784	t=      150 R=   1e+06
Depth=     847 States= 1.53e+08 Transitions= 3.31e+08 Memory=  6696.444	t=      151 R=   1e+06
Depth=     847 States= 1.54e+08 Transitions= 3.33e+08 Memory=  6723.983	t=      151 R=   1e+06
Depth=     847 States= 1.55e+08 Transitions= 3.35e+08 Memory=  6749.960	t=      152 R=   1e+06
Depth=     847 States= 1.56e+08 Transitions= 3.37e+08 Memory=  6776.718	t=      153 R=   1e+06
Depth=     847 States= 1.57e+08 Transitions= 3.39e+08 Memory=  6803.573	t=      154 R=   1e+06
Depth=     847 States= 1.58e+08 Transitions= 3.41e+08 Memory=  6830.429	t=      155 R=   1e+06
Depth=     847 States= 1.59e+08 Transitions= 3.43e+08 Memory=  6856.698	t=      156 R=   1e+06
Depth=     847 States=  1.6e+08 Transitions= 3.45e+08 Memory=  6883.358	t=      157 R=   1e+06
Depth=     847 States= 1.61e+08 Transitions= 3.47e+08 Memory=  6910.214	t=      158 R=   1e+06
Depth=     847 States= 1.62e+08 Transitions= 3.49e+08 Memory=  6936.874	t=      159 R=   1e+06
Depth=     847 States= 1.63e+08 Transitions= 3.52e+08 Memory=  6963.632	t=      160 R=   1e+06
Depth=     847 States= 1.64e+08 Transitions= 3.54e+08 Memory=  6991.269	t=      161 R=   1e+06
Depth=     847 States= 1.65e+08 Transitions= 3.57e+08 Memory=  7017.147	t=      162 R=   1e+06
Depth=     847 States= 1.66e+08 Transitions= 3.59e+08 Memory=  7043.808	t=      163 R=   1e+06
Depth=     847 States= 1.67e+08 Transitions= 3.61e+08 Memory=  7070.468	t=      164 R=   1e+06
Depth=     847 States= 1.68e+08 Transitions= 3.64e+08 Memory=  7097.909	t=      165 R=   1e+06
Depth=     847 States= 1.69e+08 Transitions= 3.66e+08 Memory=  7124.081	t=      166 R=   1e+06
Depth=     847 States=  1.7e+08 Transitions= 3.69e+08 Memory=  7150.741	t=      167 R=   1e+06
Depth=     847 States= 1.71e+08 Transitions= 3.71e+08 Memory=  7177.304	t=      168 R=   1e+06
Depth=     847 States= 1.72e+08 Transitions= 3.74e+08 Memory=  7204.159	t=      169 R=   1e+06
Depth=     847 States= 1.73e+08 Transitions= 3.76e+08 Memory=  7230.722	t=      171 R=   1e+06
Depth=     847 States= 1.74e+08 Transitions= 3.79e+08 Memory=  7257.480	t=      172 R=   1e+06
Depth=     847 States= 1.75e+08 Transitions= 3.81e+08 Memory=  7284.140	t=      173 R=   1e+06
Depth=     847 States= 1.76e+08 Transitions= 3.84e+08 Memory=  7310.897	t=      174 R=   1e+06
Depth=     847 States= 1.77e+08 Transitions= 3.87e+08 Memory=  7338.437	t=      175 R=   1e+06
Depth=     847 States= 1.78e+08 Transitions= 3.89e+08 Memory=  7364.315	t=      176 R=   1e+06
Depth=     847 States= 1.79e+08 Transitions= 3.92e+08 Memory=  7391.269	t=      177 R=   1e+06
Depth=     847 States=  1.8e+08 Transitions= 3.94e+08 Memory=  7417.929	t=      178 R=   1e+06
Depth=     847 States= 1.81e+08 Transitions= 3.97e+08 Memory=  7445.077	t=      179 R=   1e+06
Depth=     847 States= 1.82e+08 Transitions= 3.99e+08 Memory=  7471.151	t=      180 R=   1e+06
Depth=     847 States= 1.83e+08 Transitions= 4.02e+08 Memory=  7497.909	t=      181 R=   1e+06
Depth=     847 States= 1.84e+08 Transitions= 4.05e+08 Memory=  7524.569	t=      183 R=   1e+06
Depth=     847 States= 1.85e+08 Transitions= 4.07e+08 Memory=  7551.425	t=      184 R=   1e+06
Depth=     847 States= 1.86e+08 Transitions=  4.1e+08 Memory=  7577.987	t=      185 R=   1e+06
Depth=     847 States= 1.87e+08 Transitions= 4.12e+08 Memory=  7604.745	t=      186 R=   1e+06
Depth=     847 States= 1.88e+08 Transitions= 4.15e+08 Memory=  7631.405	t=      187 R=   1e+06
Depth=     847 States= 1.89e+08 Transitions= 4.17e+08 Memory=  7658.163	t=      188 R=   1e+06
Depth=     847 States=  1.9e+08 Transitions=  4.2e+08 Memory=  7684.823	t=      189 R=   1e+06
Depth=     847 States= 1.91e+08 Transitions= 4.23e+08 Memory=  7711.581	t=      190 R=   1e+06
Depth=     847 States= 1.92e+08 Transitions= 4.25e+08 Memory=  7738.339	t=      191 R=   1e+06
Depth=     847 States= 1.93e+08 Transitions= 4.28e+08 Memory=  7765.194	t=      192 R=   1e+06
Depth=     847 States= 1.94e+08 Transitions=  4.3e+08 Memory=  7791.659	t=      193 R=   1e+06
Depth=     847 States= 1.95e+08 Transitions= 4.33e+08 Memory=  7818.515	t=      194 R=   1e+06
Depth=     847 States= 1.96e+08 Transitions= 4.35e+08 Memory=  7845.077	t=      195 R=   1e+06
Depth=     847 States= 1.97e+08 Transitions= 4.38e+08 Memory=  7871.835	t=      196 R=   1e+06
Depth=     847 States= 1.98e+08 Transitions= 4.41e+08 Memory=  7898.593	t=      198 R=   1e+06
Depth=     847 States= 1.99e+08 Transitions= 4.43e+08 Memory=  7925.351	t=      199 R=   1e+06
Depth=     847 States=    2e+08 Transitions= 4.46e+08 Memory=  7952.011	t=      200 R=   1e+06
Depth=     847 States= 2.01e+08 Transitions= 4.49e+08 Memory=  7978.769	t=      201 R=   1e+06
Depth=     847 States= 2.02e+08 Transitions= 4.51e+08 Memory=  8005.429	t=      202 R=   1e+06
Depth=     847 States= 2.03e+08 Transitions= 4.54e+08 Memory=  8032.187	t=      203 R=   1e+06
Depth=     847 States= 2.04e+08 Transitions= 4.57e+08 Memory=  8059.140	t=      204 R=   1e+06
Depth=     885 States= 2.05e+08 Transitions= 4.59e+08 Memory=  8085.702	t=      205 R=   1e+06
Depth=     885 States= 2.06e+08 Transitions= 4.62e+08 Memory=  8112.948	t=      207 R=   1e+06
Depth=     885 States= 2.07e+08 Transitions= 4.65e+08 Memory=  8139.022	t=      208 R=   1e+06
Depth=     885 States= 2.08e+08 Transitions= 4.67e+08 Memory=  8165.976	t=      209 R=   1e+06
Depth=     885 States= 2.09e+08 Transitions=  4.7e+08 Memory=  8192.929	t=      210 R=   1e+06
Depth=     885 States=  2.1e+08 Transitions= 4.73e+08 Memory=  8219.198	t=      211 R=   1e+06
Depth=     885 States= 2.11e+08 Transitions= 4.75e+08 Memory=  8245.956	t=      212 R=   1e+06
Depth=     885 States= 2.12e+08 Transitions= 4.78e+08 Memory=  8272.909	t=      213 R=   1e+06
Depth=     885 States= 2.13e+08 Transitions= 4.81e+08 Memory=  8299.374	t=      214 R=   1e+06
Depth=     885 States= 2.14e+08 Transitions= 4.83e+08 Memory=  8326.132	t=      216 R=   1e+06
Depth=     885 States= 2.15e+08 Transitions= 4.86e+08 Memory=  8353.183	t=      217 R=   1e+06
Depth=     885 States= 2.16e+08 Transitions= 4.89e+08 Memory=  8379.550	t=      218 R=   1e+06
Depth=     885 States= 2.17e+08 Transitions= 4.92e+08 Memory=  8406.698	t=      219 R=   1e+06
Depth=     885 States= 2.18e+08 Transitions= 4.94e+08 Memory=  8433.065	t=      220 R=   1e+06
Depth=     885 States= 2.19e+08 Transitions= 4.97e+08 Memory=  8459.726	t=      221 R=   1e+06
Depth=     885 States=  2.2e+08 Transitions=    5e+08 Memory=  8486.581	t=      222 R=   1e+06
Depth=     885 States= 2.21e+08 Transitions= 5.02e+08 Memory=  8513.339	t=      223 R=   1e+06
Depth=     885 States= 2.22e+08 Transitions= 5.05e+08 Memory=  8539.999	t=      225 R=   1e+06
Depth=     885 States= 2.23e+08 Transitions= 5.08e+08 Memory=  8566.855	t=      226 R=   1e+06
Depth=     885 States= 2.24e+08 Transitions=  5.1e+08 Memory=  8593.710	t=      227 R=   1e+06
Depth=     885 States= 2.25e+08 Transitions= 5.13e+08 Memory=  8620.565	t=      228 R=   1e+06

(Spin Version 6.5.2 -- 6 December 2019)
	+ Partial Order Reduction
	+ Compression

Full statespace search for:
	never claim         	+ (eventually_execute)
	assertion violations	+ (if within scope of claim)
	acceptance   cycles 	+ (fairness disabled)
	invalid end states	- (disabled by never claim)

State-vector 112 byte, depth reached 885, errors: 0
1.1254972e+08 states, stored (2.25099e+08 visited)
2.8796121e+08 states, matched
5.1306064e+08 transitions (= visited+matched)
1.0661164e+08 atomic steps
hash conflicts: 1.2818065e+08 (resolved)

Stats on memory usage (in Megabytes):
15885.695	equivalent memory usage for states (stored*(State-vector + overhead))
 6575.989	actual memory usage for states (compression: 41.40%)
         	state-vector as stored = 25 byte + 36 byte overhead
 2048.000	memory used for hash table (-w28)
    0.534	memory used for DFS stack (-m10000)
    1.915	memory lost to fragmentation
 8622.616	total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:19813 2:102 3:194 4:4 5:57 6:2 ]

pan: elapsed time 228 seconds
pan: rate 987668.11 states/second
```
