# Preemptive fixed-priority scheduler that ensures priorities

This is a model of the fully-preemptive `PrioritizedFIFOScheduler` to verify that priority inversion does not occur.
Note that this does not consider inter-scheduler preemption.
We have prepared an environment that could cause the priority inversion presented in [this comments](https://github.com/tier4/awkernel/pull/255#issuecomment-2556669740).
There are two CPUs and four tasks, and the smaller the task index, the higher the priority.
Tasks are executed as follows:

1. init: wake task 3
2. (CPU 0) worker thread 0: execute task 3, wake task 2, and block.
3. (CPU 1) worker thread 1: execute task 2, wake tasks 0,1, send IPI for preemption, and block.
4. interrupt_handler: handling IPI and occur preemption.
5. ...

## Targets

- [awkernel_async_lib/src/scheduler.rs](../../../../../awkernel_async_lib/src/scheduler.rs)
- [awkernel_async_lib/src/scheduler/prioritized_fifo.rs](../../../../../awkernel_async_lib/src/scheduler/prioritized_fifo.rs)
- [awkernel_async_lib/src/task/preempt.rs](../../../../../awkernel_async_lib/src/task/preempt.rs)
- [awkernel_async_lib/src/task.rs](../../../../../awkernel_async_lib/src/task.rs)

## Subjects to be Verified

1. The all tasks are eventually terminated (`ltl eventually_terminated`).
2. The waking processing of all tasks which includes preemption is eventually completed (`ltl eventually_prerequisites`).
3. The priority of tasks is ensured unless they are within the waking processing (`ltl ensure_priority`).

## Result

`ltl eventually_terminated`

```
$ make run
spin -a preemptive.pml
ltl eventually_terminate: <> ((num_terminated==4))
gcc -O3 -DCOLLAPSE -DVECTORSZ=5000 -DNFAIR=3 -o pan pan.c
rm -f *.trail
./pan -a -n -m30000
Depth=    2473 States=    1e+06 Transitions= 2.44e+06 Memory=   166.071 t=     4.88 R=   2e+05
Depth=    2473 States=    2e+06 Transitions=  4.9e+06 Memory=   198.019 t=     9.72 R=   2e+05
Depth=    2513 States=    3e+06 Transitions= 7.35e+06 Memory=   230.921 t=     14.7 R=   2e+05
Depth=    2513 States=    4e+06 Transitions= 9.81e+06 Memory=   262.392 t=     19.8 R=   2e+05
Depth=    2513 States=    5e+06 Transitions= 1.23e+07 Memory=   293.863 t=     24.8 R=   2e+05
Depth=    2513 States=    6e+06 Transitions= 1.47e+07 Memory=   324.858 t=     29.7 R=   2e+05
Depth=    2513 States=    7e+06 Transitions= 1.72e+07 Memory=   355.375 t=     34.6 R=   2e+05
Depth=    2513 States=    8e+06 Transitions= 1.97e+07 Memory=   385.893 t=     39.7 R=   2e+05
Depth=    2513 States=    9e+06 Transitions= 2.21e+07 Memory=   416.410 t=     44.7 R=   2e+05
Depth=    2513 States=    1e+07 Transitions= 2.46e+07 Memory=   446.928 t=     49.7 R=   2e+05
Depth=    2513 States=  1.1e+07 Transitions= 2.71e+07 Memory=   477.922 t=     54.7 R=   2e+05
Depth=    2513 States=  1.2e+07 Transitions= 2.95e+07 Memory=   508.440 t=     59.8 R=   2e+05
Depth=    2513 States=  1.3e+07 Transitions=  3.2e+07 Memory=   539.911 t=     64.8 R=   2e+05
Depth=    2513 States=  1.4e+07 Transitions= 3.45e+07 Memory=   571.382 t=     69.7 R=   2e+05
Depth=    2513 States=  1.5e+07 Transitions= 3.69e+07 Memory=   601.900 t=     74.9 R=   2e+05
Depth=    2513 States=  1.6e+07 Transitions= 3.94e+07 Memory=   632.418 t=       80 R=   2e+05
Depth=    2513 States=  1.7e+07 Transitions= 4.18e+07 Memory=   663.412 t=     85.2 R=   2e+05
Depth=    2513 States=  1.8e+07 Transitions= 4.43e+07 Memory=   694.883 t=     90.1 R=   2e+05
Depth=    2513 States=  1.9e+07 Transitions= 4.67e+07 Memory=   732.553 t=     95.1 R=   2e+05
Depth=    2513 States=    2e+07 Transitions= 4.92e+07 Memory=   767.363 t=      100 R=   2e+05
Depth=    2513 States=  2.1e+07 Transitions= 5.16e+07 Memory=   801.695 t=      105 R=   2e+05
Depth=    2513 States=  2.2e+07 Transitions= 5.41e+07 Memory=   836.027 t=      110 R=   2e+05
Depth=    2513 States=  2.3e+07 Transitions= 5.65e+07 Memory=   870.836 t=      115 R=   2e+05
Depth=    2513 States=  2.4e+07 Transitions=  5.9e+07 Memory=   905.168 t=      120 R=   2e+05
Depth=    2513 States=  2.5e+07 Transitions= 6.14e+07 Memory=   939.501 t=      125 R=   2e+05
Depth=    2513 States=  2.6e+07 Transitions= 6.39e+07 Memory=   973.833 t=      130 R=   2e+05
Depth=    2513 States=  2.7e+07 Transitions= 6.64e+07 Memory=  1008.165 t=      136 R=   2e+05
Depth=    2513 States=  2.8e+07 Transitions= 6.88e+07 Memory=  1042.974 t=      140 R=   2e+05
Depth=    2513 States=  2.9e+07 Transitions= 7.13e+07 Memory=  1077.307 t=      146 R=   2e+05
Depth=    2513 States=    3e+07 Transitions= 7.38e+07 Memory=  1111.639 t=      151 R=   2e+05
Depth=    2513 States=  3.1e+07 Transitions= 7.62e+07 Memory=  1145.971 t=      156 R=   2e+05
Depth=    2513 States=  3.2e+07 Transitions= 7.87e+07 Memory=  1179.827 t=      161 R=   2e+05
Depth=    2513 States=  3.3e+07 Transitions= 8.12e+07 Memory=  1213.205 t=      166 R=   2e+05
Depth=    2513 States=  3.4e+07 Transitions= 8.37e+07 Memory=  1246.107 t=      171 R=   2e+05
pan: resizing hashtable to -w26..  done
Depth=    2513 States=  3.5e+07 Transitions= 8.62e+07 Memory=  1775.750 t=      179 R=   2e+05
Depth=    2513 States=  3.6e+07 Transitions= 8.86e+07 Memory=  1809.129 t=      184 R=   2e+05
Depth=    2513 States=  3.7e+07 Transitions= 9.11e+07 Memory=  1844.891 t=      189 R=   2e+05
Depth=    2513 States=  3.8e+07 Transitions= 9.36e+07 Memory=  1877.793 t=      194 R=   2e+05
Depth=    2513 States=  3.9e+07 Transitions=  9.6e+07 Memory=  1913.556 t=      199 R=   2e+05
Depth=    2513 States=    4e+07 Transitions= 9.85e+07 Memory=  1947.888 t=      204 R=   2e+05
Depth=    2513 States=  4.1e+07 Transitions= 1.01e+08 Memory=  1980.313 t=      209 R=   2e+05
Depth=    2513 States=  4.2e+07 Transitions= 1.03e+08 Memory=  2014.645 t=      214 R=   2e+05
Depth=    2513 States=  4.3e+07 Transitions= 1.06e+08 Memory=  2046.594 t=      219 R=   2e+05
Depth=    2513 States=  4.4e+07 Transitions= 1.08e+08 Memory=  2080.926 t=      224 R=   2e+05
Depth=    2513 States=  4.5e+07 Transitions= 1.11e+08 Memory=  2113.351 t=      229 R=   2e+05
Depth=    2513 States=  4.6e+07 Transitions= 1.13e+08 Memory=  2148.160 t=      234 R=   2e+05
Depth=    2513 States=  4.7e+07 Transitions= 1.16e+08 Memory=  2180.585 t=      239 R=   2e+05
Depth=    2513 States=  4.8e+07 Transitions= 1.18e+08 Memory=  2214.917 t=      244 R=   2e+05
Depth=    2513 States=  4.9e+07 Transitions= 1.21e+08 Memory=  2248.296 t=      249 R=   2e+05
Depth=    2513 States=    5e+07 Transitions= 1.23e+08 Memory=  2284.058 t=      254 R=   2e+05
Depth=    2513 States=  5.1e+07 Transitions= 1.26e+08 Memory=  2319.821 t=      259 R=   2e+05
Depth=    2513 States=  5.2e+07 Transitions= 1.28e+08 Memory=  2354.153 t=      264 R=   2e+05
Depth=    2527 States=  5.3e+07 Transitions=  1.3e+08 Memory=  2390.870 t=      269 R=   2e+05
Depth=    2527 States=  5.4e+07 Transitions= 1.33e+08 Memory=  2425.679 t=      274 R=   2e+05
Depth=    2527 States=  5.5e+07 Transitions= 1.35e+08 Memory=  2460.488 t=      279 R=   2e+05
Depth=    2527 States=  5.6e+07 Transitions= 1.38e+08 Memory=  2494.820 t=      284 R=   2e+05
Depth=    2527 States=  5.7e+07 Transitions=  1.4e+08 Memory=  2529.153 t=      289 R=   2e+05
Depth=    2527 States=  5.8e+07 Transitions= 1.43e+08 Memory=  2563.008 t=      294 R=   2e+05
Depth=    2527 States=  5.9e+07 Transitions= 1.45e+08 Memory=  2597.340 t=      299 R=   2e+05
Depth=    2527 States=    6e+07 Transitions= 1.48e+08 Memory=  2632.150 t=      304 R=   2e+05
Depth=    2527 States=  6.1e+07 Transitions=  1.5e+08 Memory=  2666.959 t=      309 R=   2e+05
Depth=    2527 States=  6.2e+07 Transitions= 1.53e+08 Memory=  2702.245 t=      314 R=   2e+05
Depth=    2527 States=  6.3e+07 Transitions= 1.55e+08 Memory=  2736.577 t=      319 R=   2e+05
Depth=    2527 States=  6.4e+07 Transitions= 1.58e+08 Memory=  2770.432 t=      324 R=   2e+05
Depth=    2527 States=  6.5e+07 Transitions=  1.6e+08 Memory=  2804.765 t=      329 R=   2e+05
Depth=    2527 States=  6.6e+07 Transitions= 1.62e+08 Memory=  2839.097 t=      334 R=   2e+05
Depth=    2527 States=  6.7e+07 Transitions= 1.65e+08 Memory=  2874.383 t=      339 R=   2e+05
Depth=    2527 States=  6.8e+07 Transitions= 1.67e+08 Memory=  2908.715 t=      344 R=   2e+05
Depth=    2527 States=  6.9e+07 Transitions=  1.7e+08 Memory=  2942.094 t=      348 R=   2e+05
Depth=    2527 States=    7e+07 Transitions= 1.72e+08 Memory=  2975.472 t=      354 R=   2e+05
Depth=    2527 States=  7.1e+07 Transitions= 1.75e+08 Memory=  3007.897 t=      359 R=   2e+05
Depth=    2527 States=  7.2e+07 Transitions= 1.77e+08 Memory=  3039.845 t=      364 R=   2e+05
Depth=    2527 States=  7.3e+07 Transitions=  1.8e+08 Memory=  3074.654 t=      369 R=   2e+05
Depth=    2527 States=  7.4e+07 Transitions= 1.82e+08 Memory=  3109.464 t=      374 R=   2e+05
Depth=    2527 States=  7.5e+07 Transitions= 1.85e+08 Memory=  3143.796 t=      379 R=   2e+05
Depth=    2527 States=  7.6e+07 Transitions= 1.87e+08 Memory=  3177.651 t=      384 R=   2e+05
Depth=    2527 States=  7.7e+07 Transitions=  1.9e+08 Memory=  3211.507 t=      389 R=   2e+05
Depth=    2527 States=  7.8e+07 Transitions= 1.92e+08 Memory=  3245.839 t=      394 R=   2e+05
Depth=    2527 States=  7.9e+07 Transitions= 1.95e+08 Memory=  3280.648 t=      399 R=   2e+05
Depth=    2527 States=    8e+07 Transitions= 1.97e+08 Memory=  3314.027 t=      404 R=   2e+05
Depth=    2527 States=  8.1e+07 Transitions=    2e+08 Memory=  3347.882 t=      409 R=   2e+05
Depth=    2527 States=  8.2e+07 Transitions= 2.02e+08 Memory=  3384.122 t=      414 R=   2e+05
Depth=    2527 States=  8.3e+07 Transitions= 2.05e+08 Memory=  3419.408 t=      419 R=   2e+05
Depth=    2527 States=  8.4e+07 Transitions= 2.07e+08 Memory=  3453.740 t=      424 R=   2e+05
Depth=    2527 States=  8.5e+07 Transitions= 2.09e+08 Memory=  3488.549 t=      429 R=   2e+05
Depth=    2527 States=  8.6e+07 Transitions= 2.12e+08 Memory=  3524.312 t=      434 R=   2e+05
Depth=    2527 States=  8.7e+07 Transitions= 2.14e+08 Memory=  3559.598 t=      439 R=   2e+05
Depth=    2527 States=  8.8e+07 Transitions= 2.17e+08 Memory=  3594.884 t=      445 R=   2e+05
Depth=    2527 States=  8.9e+07 Transitions= 2.19e+08 Memory=  3630.170 t=      450 R=   2e+05
Depth=    2527 States=    9e+07 Transitions= 2.22e+08 Memory=  3665.456 t=      455 R=   2e+05
Depth=    2527 States=  9.1e+07 Transitions= 2.24e+08 Memory=  3698.834 t=      460 R=   2e+05
Depth=    2527 States=  9.2e+07 Transitions= 2.27e+08 Memory=  3730.782 t=      465 R=   2e+05
Depth=    2527 States=  9.3e+07 Transitions= 2.29e+08 Memory=  3763.684 t=      470 R=   2e+05
Depth=    2527 States=  9.4e+07 Transitions= 2.32e+08 Memory=  3799.447 t=      475 R=   2e+05
Depth=    2527 States=  9.5e+07 Transitions= 2.34e+08 Memory=  3832.826 t=      481 R=   2e+05
Depth=    2527 States=  9.6e+07 Transitions= 2.36e+08 Memory=  3870.019 t=      486 R=   2e+05
Depth=    2527 States=  9.7e+07 Transitions= 2.39e+08 Memory=  3904.828 t=      491 R=   2e+05
Depth=    2527 States=  9.8e+07 Transitions= 2.41e+08 Memory=  3939.160 t=      496 R=   2e+05
Depth=    2527 States=  9.9e+07 Transitions= 2.44e+08 Memory=  3972.539 t=      501 R=   2e+05
Depth=    2527 States=    1e+08 Transitions= 2.46e+08 Memory=  4006.871 t=      507 R=   2e+05
Depth=    2527 States= 1.01e+08 Transitions= 2.49e+08 Memory=  4040.250 t=      512 R=   2e+05
Depth=    2527 States= 1.02e+08 Transitions= 2.51e+08 Memory=  4073.151 t=      517 R=   2e+05
Depth=    2527 States= 1.03e+08 Transitions= 2.54e+08 Memory=  4104.146 t=      522 R=   2e+05
Depth=    2527 States= 1.04e+08 Transitions= 2.56e+08 Memory=  4137.048 t=      528 R=   2e+05
Depth=    2527 States= 1.05e+08 Transitions= 2.59e+08 Memory=  4169.949 t=      533 R=   2e+05
Depth=    2527 States= 1.06e+08 Transitions= 2.61e+08 Memory=  4201.897 t=      538 R=   2e+05
Depth=    2527 States= 1.07e+08 Transitions= 2.64e+08 Memory=  4235.753 t=      543 R=   2e+05
Depth=    2527 States= 1.08e+08 Transitions= 2.66e+08 Memory=  4271.516 t=      548 R=   2e+05
Depth=    2527 States= 1.09e+08 Transitions= 2.69e+08 Memory=  4307.278 t=      554 R=   2e+05
Depth=    2527 States=  1.1e+08 Transitions= 2.71e+08 Memory=  4342.088 t=      559 R=   2e+05
Depth=    2527 States= 1.11e+08 Transitions= 2.73e+08 Memory=  4374.989 t=      564 R=   2e+05
Depth=    2527 States= 1.12e+08 Transitions= 2.76e+08 Memory=  4409.322 t=      569 R=   2e+05
Depth=    2527 States= 1.13e+08 Transitions= 2.78e+08 Memory=  4444.608 t=      574 R=   2e+05
Depth=    2527 States= 1.14e+08 Transitions= 2.81e+08 Memory=  4477.509 t=      580 R=   2e+05
Depth=    2527 States= 1.15e+08 Transitions= 2.83e+08 Memory=  4512.318 t=      585 R=   2e+05
Depth=    2527 States= 1.16e+08 Transitions= 2.86e+08 Memory=  4546.651 t=      590 R=   2e+05
Depth=    2527 States= 1.17e+08 Transitions= 2.88e+08 Memory=  4579.552 t=      595 R=   2e+05
Depth=    2527 States= 1.18e+08 Transitions= 2.91e+08 Memory=  4612.931 t=      600 R=   2e+05
Depth=    2527 States= 1.19e+08 Transitions= 2.93e+08 Memory=  4644.879 t=      605 R=   2e+05
Depth=    2527 States=  1.2e+08 Transitions= 2.96e+08 Memory=  4679.211 t=      610 R=   2e+05
Depth=    2527 States= 1.21e+08 Transitions= 2.98e+08 Memory=  4714.021 t=      615 R=   2e+05
Depth=    2527 States= 1.22e+08 Transitions= 3.01e+08 Memory=  4748.353 t=      620 R=   2e+05
Depth=    2527 States= 1.23e+08 Transitions= 3.03e+08 Memory=  4780.778 t=      625 R=   2e+05
Depth=    2527 States= 1.24e+08 Transitions= 3.05e+08 Memory=  4813.203 t=      630 R=   2e+05
Depth=    2527 States= 1.25e+08 Transitions= 3.08e+08 Memory=  4845.628 t=      635 R=   2e+05
Depth=    2527 States= 1.26e+08 Transitions=  3.1e+08 Memory=  4879.483 t=      641 R=   2e+05
Depth=    2527 States= 1.27e+08 Transitions= 3.13e+08 Memory=  4913.339 t=      646 R=   2e+05
Depth=    2527 States= 1.28e+08 Transitions= 3.15e+08 Memory=  4945.287 t=      651 R=   2e+05
Depth=    2527 States= 1.29e+08 Transitions= 3.18e+08 Memory=  4979.142 t=      656 R=   2e+05
Depth=    2527 States=  1.3e+08 Transitions=  3.2e+08 Memory=  5012.997 t=      661 R=   2e+05
Depth=    2527 States= 1.31e+08 Transitions= 3.23e+08 Memory=  5044.946 t=      666 R=   2e+05
Depth=    2527 States= 1.32e+08 Transitions= 3.25e+08 Memory=  5078.324 t=      671 R=   2e+05
Depth=    2527 States= 1.33e+08 Transitions= 3.28e+08 Memory=  5111.703 t=      676 R=   2e+05
Depth=    2527 States= 1.34e+08 Transitions=  3.3e+08 Memory=  5145.558 t=      682 R=   2e+05
Depth=    2527 States= 1.35e+08 Transitions= 3.32e+08 Memory=  5180.367 t=      687 R=   2e+05
pan: resizing hashtable to -w28..  done
Depth=    2527 States= 1.36e+08 Transitions= 3.35e+08 Memory=  7228.367 t=      706 R=   2e+05
Depth=    2527 States= 1.37e+08 Transitions= 3.37e+08 Memory=  7231.705 t=      711 R=   2e+05
Depth=    2527 States= 1.38e+08 Transitions=  3.4e+08 Memory=  7264.607 t=      716 R=   2e+05
Depth=    2527 States= 1.39e+08 Transitions= 3.42e+08 Memory=  7298.462 t=      721 R=   2e+05
Depth=    2527 States=  1.4e+08 Transitions= 3.45e+08 Memory=  7329.457 t=      725 R=   2e+05
Depth=    2527 States= 1.41e+08 Transitions= 3.47e+08 Memory=  7360.928 t=      730 R=   2e+05
Depth=    2527 States= 1.42e+08 Transitions=  3.5e+08 Memory=  7392.876 t=      735 R=   2e+05
Depth=    2527 States= 1.43e+08 Transitions= 3.52e+08 Memory=  7423.871 t=      740 R=   2e+05
Depth=    2527 States= 1.44e+08 Transitions= 3.55e+08 Memory=  7455.342 t=      745 R=   2e+05
Depth=    2527 States= 1.45e+08 Transitions= 3.57e+08 Memory=  7486.336 t=      750 R=   2e+05
Depth=    2527 States= 1.46e+08 Transitions=  3.6e+08 Memory=  7518.284 t=      755 R=   2e+05
Depth=    2527 States= 1.47e+08 Transitions= 3.62e+08 Memory=  7549.279 t=      761 R=   2e+05
Depth=    2527 States= 1.48e+08 Transitions= 3.64e+08 Memory=  7580.750 t=      766 R=   2e+05
Depth=    2527 States= 1.49e+08 Transitions= 3.67e+08 Memory=  7613.175 t=      771 R=   2e+05
Depth=    2527 States=  1.5e+08 Transitions= 3.69e+08 Memory=  7646.077 t=      776 R=   2e+05
Depth=    2527 States= 1.51e+08 Transitions= 3.72e+08 Memory=  7677.548 t=      781 R=   2e+05
Depth=    2527 States= 1.52e+08 Transitions= 3.74e+08 Memory=  7709.973 t=      786 R=   2e+05
Depth=    2527 States= 1.53e+08 Transitions= 3.77e+08 Memory=  7741.444 t=      791 R=   2e+05
Depth=    2527 States= 1.54e+08 Transitions= 3.79e+08 Memory=  7772.915 t=      796 R=   2e+05
Depth=    2527 States= 1.55e+08 Transitions= 3.82e+08 Memory=  7804.387 t=      801 R=   2e+05
Depth=    2527 States= 1.56e+08 Transitions= 3.84e+08 Memory=  7835.858 t=      806 R=   2e+05
Depth=    2527 States= 1.57e+08 Transitions= 3.87e+08 Memory=  7867.806 t=      811 R=   2e+05
Depth=    2527 States= 1.58e+08 Transitions= 3.89e+08 Memory=  7898.800 t=      815 R=   2e+05
Depth=    2527 States= 1.59e+08 Transitions= 3.91e+08 Memory=  7930.272 t=      820 R=   2e+05
Depth=    2527 States=  1.6e+08 Transitions= 3.94e+08 Memory=  7962.697 t=      825 R=   2e+05
Depth=    2527 States= 1.61e+08 Transitions= 3.96e+08 Memory=  7996.075 t=      830 R=   2e+05
Depth=    2527 States= 1.62e+08 Transitions= 3.99e+08 Memory=  8029.454 t=      835 R=   2e+05
Depth=    2527 States= 1.63e+08 Transitions= 4.01e+08 Memory=  8063.309 t=      840 R=   2e+05
Depth=    2527 States= 1.64e+08 Transitions= 4.04e+08 Memory=  8096.211 t=      845 R=   2e+05
Depth=    2527 States= 1.65e+08 Transitions= 4.06e+08 Memory=  8130.066 t=      850 R=   2e+05
Depth=    2527 States= 1.66e+08 Transitions= 4.09e+08 Memory=  8163.445 t=      856 R=   2e+05
Depth=    2527 States= 1.67e+08 Transitions= 4.11e+08 Memory=  8196.824 t=      861 R=   2e+05
Depth=    2527 States= 1.68e+08 Transitions= 4.14e+08 Memory=  8227.818 t=      866 R=   2e+05
Depth=    2527 States= 1.69e+08 Transitions= 4.16e+08 Memory=  8260.243 t=      871 R=   2e+05
Depth=    2527 States=  1.7e+08 Transitions= 4.19e+08 Memory=  8292.668 t=      876 R=   2e+05
Depth=    2527 States= 1.71e+08 Transitions= 4.21e+08 Memory=  8325.093 t=      881 R=   2e+05
Depth=    2527 States= 1.72e+08 Transitions= 4.24e+08 Memory=  8356.564 t=      886 R=   2e+05
Depth=    2527 States= 1.73e+08 Transitions= 4.26e+08 Memory=  8392.327 t=      891 R=   2e+05
Depth=    2527 States= 1.74e+08 Transitions= 4.28e+08 Memory=  8427.136 t=      896 R=   2e+05
Depth=    2527 States= 1.75e+08 Transitions= 4.31e+08 Memory=  8460.038 t=      901 R=   2e+05
Depth=    2527 States= 1.76e+08 Transitions= 4.33e+08 Memory=  8493.416 t=      906 R=   2e+05
Depth=    2527 States= 1.77e+08 Transitions= 4.36e+08 Memory=  8527.749 t=      911 R=   2e+05
Depth=    2527 States= 1.78e+08 Transitions= 4.38e+08 Memory=  8560.650 t=      917 R=   2e+05
Depth=    2527 States= 1.79e+08 Transitions= 4.41e+08 Memory=  8593.075 t=      922 R=   2e+05
Depth=    2527 States=  1.8e+08 Transitions= 4.43e+08 Memory=  8625.500 t=      927 R=   2e+05
Depth=    2527 States= 1.81e+08 Transitions= 4.46e+08 Memory=  8658.879 t=      932 R=   2e+05
Depth=    2527 States= 1.82e+08 Transitions= 4.48e+08 Memory=  8691.781 t=      937 R=   2e+05
Depth=    2527 States= 1.83e+08 Transitions= 4.51e+08 Memory=  8723.252 t=      941 R=   2e+05
Depth=    2527 States= 1.84e+08 Transitions= 4.53e+08 Memory=  8757.584 t=      946 R=   2e+05
Depth=    2527 States= 1.85e+08 Transitions= 4.56e+08 Memory=  8789.055 t=      951 R=   2e+05
Depth=    2527 States= 1.86e+08 Transitions= 4.58e+08 Memory=  8821.957 t=      956 R=   2e+05
Depth=    2527 States= 1.87e+08 Transitions=  4.6e+08 Memory=  8855.813 t=      961 R=   2e+05
Depth=    2527 States= 1.88e+08 Transitions= 4.63e+08 Memory=  8888.714 t=      967 R=   2e+05
Depth=    2527 States= 1.89e+08 Transitions= 4.65e+08 Memory=  8920.186 t=      972 R=   2e+05
Depth=    2527 States=  1.9e+08 Transitions= 4.68e+08 Memory=  8951.180 t=      977 R=   2e+05
Depth=    2527 States= 1.91e+08 Transitions=  4.7e+08 Memory=  8982.174 t=      981 R=   2e+05
Depth=    2527 States= 1.92e+08 Transitions= 4.73e+08 Memory=  9014.599 t=      986 R=   2e+05
Depth=    2527 States= 1.93e+08 Transitions= 4.75e+08 Memory=  9047.501 t=      991 R=   2e+05
Depth=    2527 States= 1.94e+08 Transitions= 4.78e+08 Memory=  9082.787 t=      996 R=   2e+05
Depth=    2527 States= 1.95e+08 Transitions=  4.8e+08 Memory=  9117.596 t=    1e+03 R=   2e+05
Depth=    2527 States= 1.96e+08 Transitions= 4.83e+08 Memory=  9150.975 t= 1.01e+03 R=   2e+05
Depth=    2527 States= 1.97e+08 Transitions= 4.85e+08 Memory=  9184.830 t= 1.01e+03 R=   2e+05
Depth=    2527 States= 1.98e+08 Transitions= 4.87e+08 Memory=  9218.209 t= 1.02e+03 R=   2e+05
Depth=    2527 States= 1.99e+08 Transitions=  4.9e+08 Memory=  9250.157 t= 1.02e+03 R=   2e+05
Depth=    2527 States=    2e+08 Transitions= 4.92e+08 Memory=  9285.443 t= 1.03e+03 R=   2e+05
Depth=    2527 States= 2.01e+08 Transitions= 4.95e+08 Memory=  9317.868 t= 1.03e+03 R=   2e+05
Depth=    2527 States= 2.02e+08 Transitions= 4.97e+08 Memory=  9351.723 t= 1.04e+03 R=   2e+05
Depth=    2527 States= 2.03e+08 Transitions=    5e+08 Memory=  9383.194 t= 1.04e+03 R=   2e+05
Depth=    2527 States= 2.04e+08 Transitions= 5.02e+08 Memory=  9414.666 t= 1.05e+03 R=   2e+05
Depth=    2527 States= 2.05e+08 Transitions= 5.05e+08 Memory=  9446.137 t= 1.05e+03 R=   2e+05
Depth=    2527 States= 2.06e+08 Transitions= 5.07e+08 Memory=  9477.131 t= 1.06e+03 R=   2e+05
Depth=    2527 States= 2.07e+08 Transitions=  5.1e+08 Memory=  9508.126 t= 1.06e+03 R=   2e+05
Depth=    2527 States= 2.08e+08 Transitions= 5.12e+08 Memory=  9539.120 t= 1.07e+03 R=   2e+05
Depth=    2527 States= 2.09e+08 Transitions= 5.15e+08 Memory=  9573.929 t= 1.07e+03 R=   2e+05
Depth=    2527 States=  2.1e+08 Transitions= 5.17e+08 Memory=  9608.738 t= 1.08e+03 R=   2e+05
Depth=    2527 States= 2.11e+08 Transitions= 5.19e+08 Memory=  9639.733 t= 1.08e+03 R=   2e+05
Depth=    2527 States= 2.12e+08 Transitions= 5.22e+08 Memory=  9670.727 t= 1.09e+03 R=   2e+05
Depth=    2527 States= 2.13e+08 Transitions= 5.24e+08 Memory=  9704.106 t= 1.09e+03 R=   2e+05
Depth=    2527 States= 2.14e+08 Transitions= 5.27e+08 Memory=  9737.008 t=  1.1e+03 R=   2e+05
Depth=    2527 States= 2.15e+08 Transitions= 5.29e+08 Memory=  9769.433 t=  1.1e+03 R=   2e+05
Depth=    2527 States= 2.16e+08 Transitions= 5.32e+08 Memory=  9802.811 t= 1.11e+03 R=   2e+05
Depth=    2527 States= 2.17e+08 Transitions= 5.34e+08 Memory=  9836.667 t= 1.11e+03 R=   2e+05
Depth=    2527 States= 2.18e+08 Transitions= 5.37e+08 Memory=  9867.184 t= 1.12e+03 R=   2e+05
Depth=    2527 States= 2.19e+08 Transitions= 5.39e+08 Memory=  9900.086 t= 1.12e+03 R=   2e+05
Depth=    2527 States=  2.2e+08 Transitions= 5.42e+08 Memory=  9935.849 t= 1.13e+03 R=   2e+05
Depth=    2527 States= 2.21e+08 Transitions= 5.44e+08 Memory=  9970.181 t= 1.13e+03 R=   2e+05
Depth=    2527 States= 2.22e+08 Transitions= 5.47e+08 Memory= 10004.990 t= 1.14e+03 R=   2e+05
Depth=    2527 States= 2.23e+08 Transitions= 5.49e+08 Memory= 10039.799 t= 1.14e+03 R=   2e+05
Depth=    2527 States= 2.24e+08 Transitions= 5.52e+08 Memory= 10073.178 t= 1.15e+03 R=   2e+05
Depth=    2527 States= 2.25e+08 Transitions= 5.54e+08 Memory= 10106.556 t= 1.15e+03 R=   2e+05
Depth=    2527 States= 2.26e+08 Transitions= 5.57e+08 Memory= 10140.889 t= 1.16e+03 R=   2e+05
Depth=    2527 States= 2.27e+08 Transitions= 5.59e+08 Memory= 10176.651 t= 1.16e+03 R=   2e+05
Depth=    2527 States= 2.28e+08 Transitions= 5.62e+08 Memory= 10210.030 t= 1.17e+03 R=   2e+05
Depth=    2527 States= 2.29e+08 Transitions= 5.64e+08 Memory= 10243.885 t= 1.17e+03 R=   2e+05
Depth=    2527 States=  2.3e+08 Transitions= 5.67e+08 Memory= 10277.741 t= 1.18e+03 R=   2e+05
Depth=    2527 States= 2.31e+08 Transitions= 5.69e+08 Memory= 10309.212 t= 1.18e+03 R=   2e+05
Depth=    2527 States= 2.32e+08 Transitions= 5.72e+08 Memory= 10343.068 t= 1.19e+03 R=   2e+05
Depth=    2527 States= 2.33e+08 Transitions= 5.74e+08 Memory= 10376.446 t=  1.2e+03 R=   2e+05
Depth=    2527 States= 2.34e+08 Transitions= 5.77e+08 Memory= 10410.302 t=  1.2e+03 R=   2e+05
Depth=    2527 States= 2.35e+08 Transitions= 5.79e+08 Memory= 10444.157 t= 1.21e+03 R=   2e+05
Depth=    2527 States= 2.36e+08 Transitions= 5.82e+08 Memory= 10477.059 t= 1.21e+03 R=   2e+05
Depth=    2527 States= 2.37e+08 Transitions= 5.84e+08 Memory= 10509.961 t= 1.22e+03 R=   2e+05
Depth=    2527 States= 2.38e+08 Transitions= 5.87e+08 Memory= 10542.386 t= 1.22e+03 R=   2e+05
Depth=    2527 States= 2.39e+08 Transitions= 5.89e+08 Memory= 10576.241 t= 1.23e+03 R=   2e+05
Depth=    2527 States=  2.4e+08 Transitions= 5.91e+08 Memory= 10608.666 t= 1.23e+03 R=   2e+05
Depth=    2527 States= 2.41e+08 Transitions= 5.94e+08 Memory= 10639.184 t= 1.24e+03 R=   2e+05
Depth=    2527 States= 2.42e+08 Transitions= 5.96e+08 Memory= 10669.701 t= 1.24e+03 R=   2e+05
Depth=    2527 States= 2.43e+08 Transitions= 5.99e+08 Memory= 10702.126 t= 1.25e+03 R=   2e+05
Depth=    2527 States= 2.44e+08 Transitions= 6.01e+08 Memory= 10733.120 t= 1.25e+03 R=   2e+05
Depth=    2527 States= 2.45e+08 Transitions= 6.04e+08 Memory= 10763.638 t= 1.26e+03 R=   2e+05
Depth=    2527 States= 2.46e+08 Transitions= 6.06e+08 Memory= 10796.063 t= 1.26e+03 R=   2e+05
Depth=    2527 States= 2.47e+08 Transitions= 6.09e+08 Memory= 10828.965 t= 1.27e+03 R=   2e+05
Depth=    2527 States= 2.48e+08 Transitions= 6.11e+08 Memory= 10860.436 t= 1.27e+03 R=   2e+05
Depth=    2527 States= 2.49e+08 Transitions= 6.14e+08 Memory= 10892.861 t= 1.28e+03 R=   2e+05
Depth=    2527 States=  2.5e+08 Transitions= 6.16e+08 Memory= 10925.286 t= 1.28e+03 R=   2e+05
Depth=    2527 States= 2.51e+08 Transitions= 6.19e+08 Memory= 10958.188 t= 1.29e+03 R=   2e+05
Depth=    2527 States= 2.52e+08 Transitions= 6.21e+08 Memory= 10989.182 t= 1.29e+03 R=   2e+05
Depth=    2527 States= 2.53e+08 Transitions= 6.24e+08 Memory= 11021.607 t=  1.3e+03 R=   2e+05
Depth=    2527 States= 2.54e+08 Transitions= 6.26e+08 Memory= 11054.986 t=  1.3e+03 R=   2e+05
Depth=    2527 States= 2.55e+08 Transitions= 6.29e+08 Memory= 11087.410 t= 1.31e+03 R=   2e+05
Depth=    2527 States= 2.56e+08 Transitions= 6.31e+08 Memory= 11117.928 t= 1.31e+03 R=   2e+05
Depth=    2527 States= 2.57e+08 Transitions= 6.34e+08 Memory= 11150.353 t= 1.32e+03 R=   2e+05
Depth=    2527 States= 2.58e+08 Transitions= 6.36e+08 Memory= 11187.546 t= 1.32e+03 R=   2e+05
Depth=    2527 States= 2.59e+08 Transitions= 6.39e+08 Memory= 11223.309 t= 1.33e+03 R=   2e+05
Depth=    2527 States=  2.6e+08 Transitions= 6.41e+08 Memory= 11257.164 t= 1.33e+03 R=   2e+05
Depth=    2527 States= 2.61e+08 Transitions= 6.44e+08 Memory= 11291.020 t= 1.34e+03 R=   2e+05
Depth=    2527 States= 2.62e+08 Transitions= 6.46e+08 Memory= 11323.922 t= 1.34e+03 R=   2e+05
Depth=    2527 States= 2.63e+08 Transitions= 6.48e+08 Memory= 11356.347 t= 1.35e+03 R=   2e+05
Depth=    2527 States= 2.64e+08 Transitions= 6.51e+08 Memory= 11388.295 t= 1.35e+03 R=   2e+05
Depth=    2527 States= 2.65e+08 Transitions= 6.53e+08 Memory= 11421.196 t= 1.36e+03 R=   2e+05
Depth=    2527 States= 2.66e+08 Transitions= 6.56e+08 Memory= 11454.098 t= 1.36e+03 R=   2e+05
Depth=    2527 States= 2.67e+08 Transitions= 6.58e+08 Memory= 11486.523 t= 1.37e+03 R=   2e+05
Depth=    2527 States= 2.68e+08 Transitions= 6.61e+08 Memory= 11519.425 t= 1.37e+03 R=   2e+05
Depth=    2527 States= 2.69e+08 Transitions= 6.63e+08 Memory= 11551.850 t= 1.38e+03 R=   2e+05
Depth=    2527 States=  2.7e+08 Transitions= 6.66e+08 Memory= 11584.275 t= 1.38e+03 R=   2e+05
Depth=    2527 States= 2.71e+08 Transitions= 6.68e+08 Memory= 11616.223 t= 1.39e+03 R=   2e+05
Depth=    2527 States= 2.72e+08 Transitions= 6.71e+08 Memory= 11647.694 t= 1.39e+03 R=   2e+05
Depth=    2527 States= 2.73e+08 Transitions= 6.73e+08 Memory= 11679.642 t=  1.4e+03 R=   2e+05
Depth=    2527 States= 2.74e+08 Transitions= 6.76e+08 Memory= 11711.590 t=  1.4e+03 R=   2e+05
Depth=    2527 States= 2.75e+08 Transitions= 6.78e+08 Memory= 11746.399 t= 1.41e+03 R=   2e+05
Depth=    2527 States= 2.76e+08 Transitions=  6.8e+08 Memory= 11781.685 t= 1.42e+03 R=   2e+05
Depth=    2527 States= 2.77e+08 Transitions= 6.83e+08 Memory= 11816.494 t= 1.42e+03 R=   2e+05
Depth=    2527 States= 2.78e+08 Transitions= 6.85e+08 Memory= 11853.211 t= 1.43e+03 R=   2e+05
Depth=    2527 States= 2.79e+08 Transitions= 6.88e+08 Memory= 11888.020 t= 1.43e+03 R=   2e+05
Depth=    2527 States=  2.8e+08 Transitions=  6.9e+08 Memory= 11922.352 t= 1.44e+03 R=   2e+05
Depth=    2527 States= 2.81e+08 Transitions= 6.93e+08 Memory= 11956.685 t= 1.44e+03 R=   2e+05
Depth=    2527 States= 2.82e+08 Transitions= 6.95e+08 Memory= 11991.017 t= 1.45e+03 R=   2e+05
Depth=    2527 States= 2.83e+08 Transitions= 6.98e+08 Memory= 12025.349 t= 1.45e+03 R=   2e+05
Depth=    2527 States= 2.84e+08 Transitions=    7e+08 Memory= 12059.681 t= 1.46e+03 R=   2e+05
Depth=    2527 States= 2.85e+08 Transitions= 7.03e+08 Memory= 12094.014 t= 1.46e+03 R=   2e+05
Depth=    2527 States= 2.86e+08 Transitions= 7.05e+08 Memory= 12128.346 t= 1.47e+03 R=   2e+05
Depth=    2527 States= 2.87e+08 Transitions= 7.08e+08 Memory= 12162.678 t= 1.47e+03 R=   2e+05
Depth=    2527 States= 2.88e+08 Transitions=  7.1e+08 Memory= 12197.964 t= 1.48e+03 R=   2e+05
Depth=    2527 States= 2.89e+08 Transitions= 7.12e+08 Memory= 12233.250 t= 1.48e+03 R=   2e+05
Depth=    2527 States=  2.9e+08 Transitions= 7.15e+08 Memory= 12267.582 t= 1.49e+03 R=   2e+05
Depth=    2527 States= 2.91e+08 Transitions= 7.17e+08 Memory= 12301.915 t= 1.49e+03 R=   2e+05
Depth=    2527 States= 2.92e+08 Transitions=  7.2e+08 Memory= 12336.247 t=  1.5e+03 R=   2e+05
Depth=    2527 States= 2.93e+08 Transitions= 7.22e+08 Memory= 12370.579 t=  1.5e+03 R=   2e+05
Depth=    2527 States= 2.94e+08 Transitions= 7.25e+08 Memory= 12406.819 t= 1.51e+03 R=   2e+05
Depth=    2527 States= 2.95e+08 Transitions= 7.27e+08 Memory= 12441.628 t= 1.51e+03 R=   2e+05
Depth=    2527 States= 2.96e+08 Transitions=  7.3e+08 Memory= 12477.868 t= 1.52e+03 R=   2e+05
Depth=    2527 States= 2.97e+08 Transitions= 7.32e+08 Memory= 12512.677 t= 1.52e+03 R=   2e+05
Depth=    2527 States= 2.98e+08 Transitions= 7.35e+08 Memory= 12547.009 t= 1.53e+03 R=   2e+05
Depth=    2527 States= 2.99e+08 Transitions= 7.37e+08 Memory= 12581.341 t= 1.53e+03 R=   2e+05
Depth=    2527 States=    3e+08 Transitions=  7.4e+08 Memory= 12615.674 t= 1.54e+03 R=   2e+05
Depth=    2527 States= 3.01e+08 Transitions= 7.42e+08 Memory= 12650.006 t= 1.55e+03 R=   2e+05
Depth=    2527 States= 3.02e+08 Transitions= 7.44e+08 Memory= 12684.338 t= 1.55e+03 R=   2e+05
Depth=    2527 States= 3.03e+08 Transitions= 7.47e+08 Memory= 12719.147 t= 1.56e+03 R=   2e+05
Depth=    2527 States= 3.04e+08 Transitions= 7.49e+08 Memory= 12754.433 t= 1.56e+03 R=   2e+05
Depth=    2527 States= 3.05e+08 Transitions= 7.52e+08 Memory= 12788.289 t= 1.57e+03 R=   2e+05
Depth=    2527 States= 3.06e+08 Transitions= 7.54e+08 Memory= 12822.621 t= 1.57e+03 R=   2e+05
Depth=    2527 States= 3.07e+08 Transitions= 7.57e+08 Memory= 12858.860 t= 1.58e+03 R=   2e+05
Depth=    2527 States= 3.08e+08 Transitions= 7.59e+08 Memory= 12894.146 t= 1.58e+03 R=   2e+05
Depth=    2527 States= 3.09e+08 Transitions= 7.62e+08 Memory= 12928.956 t= 1.59e+03 R=   2e+05
Depth=    2527 States=  3.1e+08 Transitions= 7.64e+08 Memory= 12965.195 t= 1.59e+03 R=   2e+05
Depth=    2527 States= 3.11e+08 Transitions= 7.67e+08 Memory= 12999.527 t=  1.6e+03 R=   2e+05
Depth=    2527 States= 3.12e+08 Transitions= 7.69e+08 Memory= 13033.860 t=  1.6e+03 R=   2e+05
Depth=    2527 States= 3.13e+08 Transitions= 7.72e+08 Memory= 13068.192 t= 1.61e+03 R=   2e+05
Depth=    2527 States= 3.14e+08 Transitions= 7.74e+08 Memory= 13102.524 t= 1.61e+03 R=   2e+05
Depth=    2527 States= 3.15e+08 Transitions= 7.76e+08 Memory= 13137.333 t= 1.62e+03 R=   2e+05
Depth=    2527 States= 3.16e+08 Transitions= 7.79e+08 Memory= 13171.666 t= 1.62e+03 R=   2e+05
Depth=    2527 States= 3.17e+08 Transitions= 7.81e+08 Memory= 13205.998 t= 1.63e+03 R=   2e+05
Depth=    2527 States= 3.18e+08 Transitions= 7.84e+08 Memory= 13240.807 t= 1.63e+03 R=   2e+05
Depth=    2527 States= 3.19e+08 Transitions= 7.86e+08 Memory= 13276.093 t= 1.64e+03 R=   2e+05
Depth=    2527 States=  3.2e+08 Transitions= 7.89e+08 Memory= 13310.425 t= 1.64e+03 R=   2e+05
Depth=    2527 States= 3.21e+08 Transitions= 7.91e+08 Memory= 13344.758 t= 1.65e+03 R=   2e+05
Depth=    2527 States= 3.22e+08 Transitions= 7.94e+08 Memory= 13380.043 t= 1.65e+03 R=   2e+05
Depth=    2527 States= 3.23e+08 Transitions= 7.96e+08 Memory= 13414.853 t= 1.66e+03 R=   2e+05
Depth=    2527 States= 3.24e+08 Transitions= 7.99e+08 Memory= 13449.185 t= 1.66e+03 R=   2e+05
Depth=    2527 States= 3.25e+08 Transitions= 8.01e+08 Memory= 13485.424 t= 1.67e+03 R=   2e+05
Depth=    2527 States= 3.26e+08 Transitions= 8.04e+08 Memory= 13520.234 t= 1.67e+03 R=   2e+05
Depth=    2527 States= 3.27e+08 Transitions= 8.06e+08 Memory= 13553.612 t= 1.68e+03 R=   2e+05
Depth=    2527 States= 3.28e+08 Transitions= 8.09e+08 Memory= 13586.514 t= 1.68e+03 R=   2e+05
Depth=    2527 States= 3.29e+08 Transitions= 8.11e+08 Memory= 13618.939 t= 1.69e+03 R=   2e+05
Depth=    2527 States=  3.3e+08 Transitions= 8.13e+08 Memory= 13654.702 t= 1.69e+03 R=   2e+05
Depth=    2527 States= 3.31e+08 Transitions= 8.16e+08 Memory= 13689.988 t=  1.7e+03 R=   2e+05
Depth=    2527 States= 3.32e+08 Transitions= 8.18e+08 Memory= 13724.797 t=  1.7e+03 R=   2e+05
Depth=    2527 States= 3.33e+08 Transitions= 8.21e+08 Memory= 13759.129 t= 1.71e+03 R=   2e+05
Depth=    2527 States= 3.34e+08 Transitions= 8.23e+08 Memory= 13793.938 t= 1.71e+03 R=   2e+05
Depth=    2527 States= 3.35e+08 Transitions= 8.26e+08 Memory= 13829.701 t= 1.72e+03 R=   2e+05
Depth=    2527 States= 3.36e+08 Transitions= 8.28e+08 Memory= 13864.987 t= 1.73e+03 R=   2e+05
Depth=    2527 States= 3.37e+08 Transitions= 8.31e+08 Memory= 13899.319 t= 1.73e+03 R=   2e+05
Depth=    2527 States= 3.38e+08 Transitions= 8.33e+08 Memory= 13934.128 t= 1.74e+03 R=   2e+05
Depth=    2527 States= 3.39e+08 Transitions= 8.36e+08 Memory= 13970.368 t= 1.74e+03 R=   2e+05
Depth=    2527 States=  3.4e+08 Transitions= 8.38e+08 Memory= 14005.654 t= 1.75e+03 R=   2e+05
Depth=    2527 States= 3.41e+08 Transitions= 8.41e+08 Memory= 14039.986 t= 1.75e+03 R=   2e+05
Depth=    2527 States= 3.42e+08 Transitions= 8.43e+08 Memory= 14074.795 t= 1.76e+03 R=   2e+05
Depth=    2527 States= 3.43e+08 Transitions= 8.46e+08 Memory= 14109.604 t= 1.76e+03 R=   2e+05
Depth=    2527 States= 3.44e+08 Transitions= 8.48e+08 Memory= 14145.844 t= 1.77e+03 R=   2e+05
Depth=    2527 States= 3.45e+08 Transitions= 8.51e+08 Memory= 14181.607 t= 1.77e+03 R=   2e+05
Depth=    2527 States= 3.46e+08 Transitions= 8.53e+08 Memory= 14217.370 t= 1.78e+03 R=   2e+05
Depth=    2527 States= 3.47e+08 Transitions= 8.55e+08 Memory= 14253.609 t= 1.78e+03 R=   2e+05
Depth=    2527 States= 3.48e+08 Transitions= 8.58e+08 Memory= 14288.418 t= 1.79e+03 R=   2e+05
Depth=    2527 States= 3.49e+08 Transitions=  8.6e+08 Memory= 14321.797 t= 1.79e+03 R=   2e+05
Depth=    2527 States=  3.5e+08 Transitions= 8.63e+08 Memory= 14356.606 t=  1.8e+03 R=   2e+05
Depth=    2527 States= 3.51e+08 Transitions= 8.65e+08 Memory= 14393.322 t=  1.8e+03 R=   2e+05
Depth=    2527 States= 3.52e+08 Transitions= 8.68e+08 Memory= 14430.039 t= 1.81e+03 R=   2e+05
Depth=    2527 States= 3.53e+08 Transitions=  8.7e+08 Memory= 14465.802 t= 1.81e+03 R=   2e+05
Depth=    2527 States= 3.54e+08 Transitions= 8.73e+08 Memory= 14501.564 t= 1.82e+03 R=   2e+05
Depth=    2527 States= 3.55e+08 Transitions= 8.75e+08 Memory= 14536.850 t= 1.82e+03 R=   2e+05
Depth=    2527 States= 3.56e+08 Transitions= 8.78e+08 Memory= 14574.044 t= 1.83e+03 R=   2e+05
Depth=    2527 States= 3.57e+08 Transitions=  8.8e+08 Memory= 14609.807 t= 1.83e+03 R=   2e+05
Depth=    2527 States= 3.58e+08 Transitions= 8.83e+08 Memory= 14646.046 t= 1.84e+03 R=   2e+05
Depth=    2527 States= 3.59e+08 Transitions= 8.85e+08 Memory= 14679.902 t= 1.84e+03 R=   2e+05
Depth=    2527 States=  3.6e+08 Transitions= 8.87e+08 Memory= 14714.711 t= 1.85e+03 R=   2e+05
Depth=    2527 States= 3.61e+08 Transitions=  8.9e+08 Memory= 14748.566 t= 1.85e+03 R=   2e+05
Depth=    2527 States= 3.62e+08 Transitions= 8.92e+08 Memory= 14786.236 t= 1.86e+03 R=   2e+05
Depth=    2527 States= 3.63e+08 Transitions= 8.95e+08 Memory= 14821.522 t= 1.86e+03 R=   2e+05
Depth=    2527 States= 3.64e+08 Transitions= 8.97e+08 Memory= 14855.854 t= 1.87e+03 R=   2e+05
Depth=    2527 States= 3.65e+08 Transitions=    9e+08 Memory= 14892.571 t= 1.88e+03 R=   2e+05
Depth=    2527 States= 3.66e+08 Transitions= 9.02e+08 Memory= 14928.334 t= 1.88e+03 R=   2e+05
Depth=    2527 States= 3.67e+08 Transitions= 9.05e+08 Memory= 14965.527 t= 1.89e+03 R=   2e+05
Depth=    2527 States= 3.68e+08 Transitions= 9.07e+08 Memory= 15000.813 t= 1.89e+03 R=   2e+05
Depth=    2527 States= 3.69e+08 Transitions=  9.1e+08 Memory= 15036.576 t=  1.9e+03 R=   2e+05
Depth=    2527 States=  3.7e+08 Transitions= 9.12e+08 Memory= 15073.292 t=  1.9e+03 R=   2e+05
Depth=    2527 States= 3.71e+08 Transitions= 9.15e+08 Memory= 15108.578 t= 1.91e+03 R=   2e+05
Depth=    2527 States= 3.72e+08 Transitions= 9.17e+08 Memory= 15144.818 t= 1.91e+03 R=   2e+05
Depth=    2527 States= 3.73e+08 Transitions= 9.19e+08 Memory= 15181.534 t= 1.92e+03 R=   2e+05
Depth=    2527 States= 3.74e+08 Transitions= 9.22e+08 Memory= 15217.297 t= 1.92e+03 R=   2e+05
Depth=    2527 States= 3.75e+08 Transitions= 9.24e+08 Memory= 15253.060 t= 1.93e+03 R=   2e+05
Depth=    2527 States= 3.76e+08 Transitions= 9.27e+08 Memory= 15287.869 t= 1.93e+03 R=   2e+05
Depth=    2527 States= 3.77e+08 Transitions= 9.29e+08 Memory= 15322.678 t= 1.94e+03 R=   2e+05
Depth=    2527 States= 3.78e+08 Transitions= 9.32e+08 Memory= 15357.487 t= 1.94e+03 R=   2e+05
Depth=    2527 States= 3.79e+08 Transitions= 9.34e+08 Memory= 15394.680 t= 1.95e+03 R=   2e+05
Depth=    2527 States=  3.8e+08 Transitions= 9.37e+08 Memory= 15431.397 t= 1.95e+03 R=   2e+05
Depth=    2527 States= 3.81e+08 Transitions= 9.39e+08 Memory= 15467.160 t= 1.96e+03 R=   2e+05
Depth=    2527 States= 3.82e+08 Transitions= 9.42e+08 Memory= 15504.353 t= 1.96e+03 R=   2e+05
Depth=    2527 States= 3.83e+08 Transitions= 9.44e+08 Memory= 15540.593 t= 1.97e+03 R=   2e+05
Depth=    2527 States= 3.84e+08 Transitions= 9.46e+08 Memory= 15577.309 t= 1.97e+03 R=   2e+05
Depth=    2527 States= 3.85e+08 Transitions= 9.49e+08 Memory= 15612.595 t= 1.98e+03 R=   2e+05
Depth=    2527 States= 3.86e+08 Transitions= 9.51e+08 Memory= 15649.312 t= 1.98e+03 R=   2e+05
Depth=    2527 States= 3.87e+08 Transitions= 9.54e+08 Memory= 15684.597 t= 1.99e+03 R=   2e+05
Depth=    2527 States= 3.88e+08 Transitions= 9.56e+08 Memory= 15721.314 t= 1.99e+03 R=   2e+05
Depth=    2527 States= 3.89e+08 Transitions= 9.59e+08 Memory= 15758.984 t=    2e+03 R=   2e+05
Depth=    2527 States=  3.9e+08 Transitions= 9.61e+08 Memory= 15795.224 t=    2e+03 R=   2e+05
Depth=    2527 States= 3.91e+08 Transitions= 9.64e+08 Memory= 15831.463 t= 2.01e+03 R=   2e+05
Depth=    2527 States= 3.92e+08 Transitions= 9.66e+08 Memory= 15868.180 t= 2.02e+03 R=   2e+05
Depth=    2527 States= 3.93e+08 Transitions= 9.69e+08 Memory= 15902.989 t= 2.02e+03 R=   2e+05
Depth=    2527 States= 3.94e+08 Transitions= 9.71e+08 Memory= 15939.229 t= 2.03e+03 R=   2e+05
Depth=    2527 States= 3.95e+08 Transitions= 9.74e+08 Memory= 15973.561 t= 2.03e+03 R=   2e+05
Depth=    2527 States= 3.96e+08 Transitions= 9.76e+08 Memory= 16007.893 t= 2.04e+03 R=   2e+05
Depth=    2527 States= 3.97e+08 Transitions= 9.78e+08 Memory= 16043.179 t= 2.04e+03 R=   2e+05
Depth=    2527 States= 3.98e+08 Transitions= 9.81e+08 Memory= 16077.511 t= 2.05e+03 R=   2e+05
Depth=    2527 States= 3.99e+08 Transitions= 9.83e+08 Memory= 16111.844 t= 2.05e+03 R=   2e+05
Depth=    2527 States=    4e+08 Transitions= 9.86e+08 Memory= 16146.176 t= 2.06e+03 R=   2e+05
Depth=    2527 States= 4.01e+08 Transitions= 9.88e+08 Memory= 16180.031 t= 2.06e+03 R=   2e+05
Depth=    2527 States= 4.02e+08 Transitions= 9.91e+08 Memory= 16214.840 t= 2.07e+03 R=   2e+05
Depth=    2527 States= 4.03e+08 Transitions= 9.93e+08 Memory= 16249.173 t= 2.07e+03 R=   2e+05
Depth=    2527 States= 4.04e+08 Transitions= 9.96e+08 Memory= 16283.028 t= 2.08e+03 R=   2e+05
Depth=    2527 States= 4.05e+08 Transitions= 9.98e+08 Memory= 16317.360 t= 2.08e+03 R=   2e+05
Depth=    2527 States= 4.06e+08 Transitions=    1e+09 Memory= 16353.123 t= 2.09e+03 R=   2e+05
Depth=    2527 States= 4.07e+08 Transitions=    1e+09 Memory= 16389.363 t= 2.09e+03 R=   2e+05
Depth=    2527 States= 4.08e+08 Transitions= 1.01e+09 Memory= 16424.649 t=  2.1e+03 R=   2e+05
Depth=    2527 States= 4.09e+08 Transitions= 1.01e+09 Memory= 16460.412 t=  2.1e+03 R=   2e+05
Depth=    2527 States=  4.1e+08 Transitions= 1.01e+09 Memory= 16494.744 t= 2.11e+03 R=   2e+05
Depth=    2527 States= 4.11e+08 Transitions= 1.01e+09 Memory= 16529.076 t= 2.11e+03 R=   2e+05
Depth=    2527 States= 4.12e+08 Transitions= 1.02e+09 Memory= 16563.408 t= 2.12e+03 R=   2e+05
Depth=    2527 States= 4.13e+08 Transitions= 1.02e+09 Memory= 16597.741 t= 2.12e+03 R=   2e+05
Depth=    2527 States= 4.14e+08 Transitions= 1.02e+09 Memory= 16632.073 t= 2.13e+03 R=   2e+05
Depth=    2527 States= 4.15e+08 Transitions= 1.02e+09 Memory= 16666.405 t= 2.13e+03 R=   2e+05
Depth=    2527 States= 4.16e+08 Transitions= 1.03e+09 Memory= 16700.737 t= 2.14e+03 R=   2e+05
Depth=    2527 States= 4.17e+08 Transitions= 1.03e+09 Memory= 16735.070 t= 2.15e+03 R=   2e+05
Depth=    2527 States= 4.18e+08 Transitions= 1.03e+09 Memory= 16770.356 t= 2.15e+03 R=   2e+05
Depth=    2527 States= 4.19e+08 Transitions= 1.03e+09 Memory= 16806.595 t= 2.16e+03 R=   2e+05
Depth=    2527 States=  4.2e+08 Transitions= 1.04e+09 Memory= 16843.789 t= 2.16e+03 R=   2e+05
Depth=    2527 States= 4.21e+08 Transitions= 1.04e+09 Memory= 16880.028 t= 2.17e+03 R=   2e+05
Depth=    2527 States= 4.22e+08 Transitions= 1.04e+09 Memory= 16917.222 t= 2.17e+03 R=   2e+05
Depth=    2527 States= 4.23e+08 Transitions= 1.04e+09 Memory= 16952.984 t= 2.18e+03 R=   2e+05
Depth=    2527 States= 4.24e+08 Transitions= 1.04e+09 Memory= 16987.793 t= 2.18e+03 R=   2e+05
Depth=    2527 States= 4.25e+08 Transitions= 1.05e+09 Memory= 17022.603 t= 2.19e+03 R=   2e+05
Depth=    2527 States= 4.26e+08 Transitions= 1.05e+09 Memory= 17056.935 t= 2.19e+03 R=   2e+05
Depth=    2527 States= 4.27e+08 Transitions= 1.05e+09 Memory= 17091.267 t=  2.2e+03 R=   2e+05
Depth=    2527 States= 4.28e+08 Transitions= 1.05e+09 Memory= 17125.599 t=  2.2e+03 R=   2e+05
Depth=    2527 States= 4.29e+08 Transitions= 1.06e+09 Memory= 17159.932 t= 2.21e+03 R=   2e+05
Depth=    2527 States=  4.3e+08 Transitions= 1.06e+09 Memory= 17196.648 t= 2.21e+03 R=   2e+05
Depth=    2527 States= 4.31e+08 Transitions= 1.06e+09 Memory= 17231.457 t= 2.22e+03 R=   2e+05
Depth=    2527 States= 4.32e+08 Transitions= 1.06e+09 Memory= 17267.220 t= 2.22e+03 R=   2e+05
Depth=    2527 States= 4.33e+08 Transitions= 1.07e+09 Memory= 17301.552 t= 2.23e+03 R=   2e+05
Depth=    2527 States= 4.34e+08 Transitions= 1.07e+09 Memory= 17335.885 t= 2.23e+03 R=   2e+05
Depth=    2527 States= 4.35e+08 Transitions= 1.07e+09 Memory= 17370.217 t= 2.24e+03 R=   2e+05
Depth=    2527 States= 4.36e+08 Transitions= 1.07e+09 Memory= 17405.503 t= 2.24e+03 R=   2e+05
Depth=    2527 States= 4.37e+08 Transitions= 1.08e+09 Memory= 17440.789 t= 2.25e+03 R=   2e+05
Depth=    2527 States= 4.38e+08 Transitions= 1.08e+09 Memory= 17476.552 t= 2.25e+03 R=   2e+05
Depth=    2527 States= 4.39e+08 Transitions= 1.08e+09 Memory= 17511.361 t= 2.26e+03 R=   2e+05
Depth=    2527 States=  4.4e+08 Transitions= 1.08e+09 Memory= 17545.693 t= 2.27e+03 R=   2e+05
Depth=    2527 States= 4.41e+08 Transitions= 1.09e+09 Memory= 17581.456 t= 2.27e+03 R=   2e+05
Depth=    2527 States= 4.42e+08 Transitions= 1.09e+09 Memory= 17618.172 t= 2.28e+03 R=   2e+05
Depth=    2527 States= 4.43e+08 Transitions= 1.09e+09 Memory= 17654.412 t= 2.28e+03 R=   2e+05
Depth=    2527 States= 4.44e+08 Transitions= 1.09e+09 Memory= 17690.651 t= 2.29e+03 R=   2e+05
Depth=    2527 States= 4.45e+08 Transitions=  1.1e+09 Memory= 17725.461 t= 2.29e+03 R=   2e+05
Depth=    2527 States= 4.46e+08 Transitions=  1.1e+09 Memory= 17761.700 t=  2.3e+03 R=   2e+05
Depth=    2527 States= 4.47e+08 Transitions=  1.1e+09 Memory= 17795.556 t=  2.3e+03 R=   2e+05
Depth=    2527 States= 4.48e+08 Transitions=  1.1e+09 Memory= 17829.888 t= 2.31e+03 R=   2e+05
Depth=    2527 States= 4.49e+08 Transitions= 1.11e+09 Memory= 17867.081 t= 2.31e+03 R=   2e+05
Depth=    2527 States=  4.5e+08 Transitions= 1.11e+09 Memory= 17902.844 t= 2.32e+03 R=   2e+05
Depth=    2527 States= 4.51e+08 Transitions= 1.11e+09 Memory= 17938.130 t= 2.32e+03 R=   2e+05
Depth=    2527 States= 4.52e+08 Transitions= 1.11e+09 Memory= 17975.323 t= 2.33e+03 R=   2e+05
Depth=    2527 States= 4.53e+08 Transitions= 1.12e+09 Memory= 18011.563 t= 2.33e+03 R=   2e+05
Depth=    2527 States= 4.54e+08 Transitions= 1.12e+09 Memory= 18047.802 t= 2.34e+03 R=   2e+05
Depth=    2527 States= 4.55e+08 Transitions= 1.12e+09 Memory= 18084.042 t= 2.34e+03 R=   2e+05
Depth=    2527 States= 4.56e+08 Transitions= 1.12e+09 Memory= 18120.759 t= 2.35e+03 R=   2e+05
Depth=    2527 States= 4.57e+08 Transitions= 1.13e+09 Memory= 18157.475 t= 2.35e+03 R=   2e+05
Depth=    2527 States= 4.58e+08 Transitions= 1.13e+09 Memory= 18193.715 t= 2.36e+03 R=   2e+05
Depth=    2527 States= 4.59e+08 Transitions= 1.13e+09 Memory= 18228.524 t= 2.36e+03 R=   2e+05
Depth=    2527 States=  4.6e+08 Transitions= 1.13e+09 Memory= 18264.763 t= 2.37e+03 R=   2e+05
Depth=    2527 States= 4.61e+08 Transitions= 1.14e+09 Memory= 18299.096 t= 2.37e+03 R=   2e+05
Depth=    2527 States= 4.62e+08 Transitions= 1.14e+09 Memory= 18332.474 t= 2.38e+03 R=   2e+05
Depth=    2527 States= 4.63e+08 Transitions= 1.14e+09 Memory= 18366.806 t= 2.38e+03 R=   2e+05
Depth=    2527 States= 4.64e+08 Transitions= 1.14e+09 Memory= 18401.139 t= 2.39e+03 R=   2e+05
Depth=    2527 States= 4.65e+08 Transitions= 1.15e+09 Memory= 18434.517 t=  2.4e+03 R=   2e+05
Depth=    2527 States= 4.66e+08 Transitions= 1.15e+09 Memory= 18468.850 t=  2.4e+03 R=   2e+05
Depth=    2527 States= 4.67e+08 Transitions= 1.15e+09 Memory= 18504.612 t= 2.41e+03 R=   2e+05
Depth=    2527 States= 4.68e+08 Transitions= 1.15e+09 Memory= 18537.991 t= 2.41e+03 R=   2e+05
Depth=    2527 States= 4.69e+08 Transitions= 1.16e+09 Memory= 18570.893 t= 2.42e+03 R=   2e+05
Depth=    2527 States=  4.7e+08 Transitions= 1.16e+09 Memory= 18606.179 t= 2.42e+03 R=   2e+05
Depth=    2527 States= 4.71e+08 Transitions= 1.16e+09 Memory= 18641.465 t= 2.43e+03 R=   2e+05
Depth=    2527 States= 4.72e+08 Transitions= 1.16e+09 Memory= 18675.797 t= 2.43e+03 R=   2e+05
Depth=    2527 States= 4.73e+08 Transitions= 1.17e+09 Memory= 18710.606 t= 2.44e+03 R=   2e+05
Depth=    2527 States= 4.74e+08 Transitions= 1.17e+09 Memory= 18747.323 t= 2.44e+03 R=   2e+05
Depth=    2527 States= 4.75e+08 Transitions= 1.17e+09 Memory= 18781.655 t= 2.45e+03 R=   2e+05
Depth=    2527 States= 4.76e+08 Transitions= 1.17e+09 Memory= 18817.894 t= 2.45e+03 R=   2e+05
Depth=    2527 States= 4.77e+08 Transitions= 1.18e+09 Memory= 18853.657 t= 2.46e+03 R=   2e+05
Depth=    2527 States= 4.78e+08 Transitions= 1.18e+09 Memory= 18887.990 t= 2.46e+03 R=   2e+05
Depth=    2527 States= 4.79e+08 Transitions= 1.18e+09 Memory= 18923.275 t= 2.47e+03 R=   2e+05
Depth=    2527 States=  4.8e+08 Transitions= 1.18e+09 Memory= 18959.515 t= 2.47e+03 R=   2e+05
Depth=    2527 States= 4.81e+08 Transitions= 1.19e+09 Memory= 18994.801 t= 2.48e+03 R=   2e+05
Depth=    2527 States= 4.82e+08 Transitions= 1.19e+09 Memory= 19030.564 t= 2.49e+03 R=   2e+05
Depth=    2527 States= 4.83e+08 Transitions= 1.19e+09 Memory= 19066.803 t= 2.49e+03 R=   2e+05
Depth=    2527 States= 4.84e+08 Transitions= 1.19e+09 Memory= 19103.520 t=  2.5e+03 R=   2e+05
Depth=    2527 States= 4.85e+08 Transitions=  1.2e+09 Memory= 19139.283 t=  2.5e+03 R=   2e+05
Depth=    2527 States= 4.86e+08 Transitions=  1.2e+09 Memory= 19175.999 t= 2.51e+03 R=   2e+05
Depth=    2527 States= 4.87e+08 Transitions=  1.2e+09 Memory= 19213.192 t= 2.51e+03 R=   2e+05
Depth=    2527 States= 4.88e+08 Transitions=  1.2e+09 Memory= 19249.909 t= 2.52e+03 R=   2e+05
Depth=    2527 States= 4.89e+08 Transitions= 1.21e+09 Memory= 19287.579 t= 2.52e+03 R=   2e+05
Depth=    2527 States=  4.9e+08 Transitions= 1.21e+09 Memory= 19326.203 t= 2.53e+03 R=   2e+05
Depth=    2527 States= 4.91e+08 Transitions= 1.21e+09 Memory= 19363.396 t= 2.53e+03 R=   2e+05
Depth=    2527 States= 4.92e+08 Transitions= 1.21e+09 Memory= 19401.066 t= 2.54e+03 R=   2e+05
Depth=    2527 States= 4.93e+08 Transitions= 1.22e+09 Memory= 19438.736 t= 2.54e+03 R=   2e+05
Depth=    2527 States= 4.94e+08 Transitions= 1.22e+09 Memory= 19475.930 t= 2.55e+03 R=   2e+05
Depth=    2527 States= 4.95e+08 Transitions= 1.22e+09 Memory= 19514.077 t= 2.55e+03 R=   2e+05
Depth=    2527 States= 4.96e+08 Transitions= 1.22e+09 Memory= 19549.839 t= 2.56e+03 R=   2e+05
Depth=    2527 States= 4.97e+08 Transitions= 1.23e+09 Memory= 19584.649 t= 2.57e+03 R=   2e+05
Depth=    2527 States= 4.98e+08 Transitions= 1.23e+09 Memory= 19618.981 t= 2.57e+03 R=   2e+05
Depth=    2527 States= 4.99e+08 Transitions= 1.23e+09 Memory= 19654.267 t= 2.58e+03 R=   2e+05
Depth=    2527 States=    5e+08 Transitions= 1.23e+09 Memory= 19690.030 t= 2.58e+03 R=   2e+05
Depth=    2527 States= 5.01e+08 Transitions= 1.24e+09 Memory= 19724.362 t= 2.59e+03 R=   2e+05
Depth=    2527 States= 5.02e+08 Transitions= 1.24e+09 Memory= 19758.694 t= 2.59e+03 R=   2e+05
Depth=    2527 States= 5.03e+08 Transitions= 1.24e+09 Memory= 19795.887 t=  2.6e+03 R=   2e+05
Depth=    2527 States= 5.04e+08 Transitions= 1.24e+09 Memory= 19833.081 t=  2.6e+03 R=   2e+05
Depth=    2527 States= 5.05e+08 Transitions= 1.25e+09 Memory= 19868.367 t= 2.61e+03 R=   2e+05
Depth=    2527 States= 5.06e+08 Transitions= 1.25e+09 Memory= 19904.129 t= 2.61e+03 R=   2e+05
Depth=    2527 States= 5.07e+08 Transitions= 1.25e+09 Memory= 19939.892 t= 2.62e+03 R=   2e+05
Depth=    2527 States= 5.08e+08 Transitions= 1.25e+09 Memory= 19977.086 t= 2.62e+03 R=   2e+05
Depth=    2527 States= 5.09e+08 Transitions= 1.25e+09 Memory= 20012.848 t= 2.63e+03 R=   2e+05
Depth=    2527 States=  5.1e+08 Transitions= 1.26e+09 Memory= 20049.088 t= 2.63e+03 R=   2e+05
Depth=    2527 States= 5.11e+08 Transitions= 1.26e+09 Memory= 20087.235 t= 2.64e+03 R=   2e+05
Depth=    2527 States= 5.12e+08 Transitions= 1.26e+09 Memory= 20122.521 t= 2.65e+03 R=   2e+05
Depth=    2527 States= 5.13e+08 Transitions= 1.26e+09 Memory= 20156.376 t= 2.65e+03 R=   2e+05
Depth=    2527 States= 5.14e+08 Transitions= 1.27e+09 Memory= 20193.570 t= 2.66e+03 R=   2e+05
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
Depth=    2494 States=    2e+06 Transitions= 4.75e+06 Memory=   197.542 t=     10.8 R=   2e+05
Depth=    2494 States=    3e+06 Transitions= 7.16e+06 Memory=   229.013 t=     16.4 R=   2e+05
Depth=    2494 States=    4e+06 Transitions= 9.58e+06 Memory=   261.438 t=     22.1 R=   2e+05
Depth=    2494 States=    5e+06 Transitions=  1.2e+07 Memory=   291.956 t=     27.7 R=   2e+05
Depth=    2494 States=    6e+06 Transitions= 1.44e+07 Memory=   322.473 t=     33.4 R=   2e+05
Depth=    2494 States=    7e+06 Transitions= 1.68e+07 Memory=   352.991 t=     39.1 R=   2e+05
Depth=    2494 States=    8e+06 Transitions= 1.92e+07 Memory=   383.509 t=     44.9 R=   2e+05
Depth=    2494 States=    9e+06 Transitions= 2.16e+07 Memory=   414.980 t=     50.6 R=   2e+05
Depth=    2494 States=    1e+07 Transitions= 2.41e+07 Memory=   446.451 t=     56.3 R=   2e+05
Depth=    2494 States=  1.1e+07 Transitions= 2.65e+07 Memory=   476.969 t=     61.9 R=   2e+05
Depth=    2494 States=  1.2e+07 Transitions= 2.89e+07 Memory=   507.963 t=     67.7 R=   2e+05
Depth=    2494 States=  1.3e+07 Transitions= 3.12e+07 Memory=   541.342 t=     73.2 R=   2e+05
Depth=    2494 States=  1.4e+07 Transitions= 3.36e+07 Memory=   573.290 t=     78.8 R=   2e+05
Depth=    2494 States=  1.5e+07 Transitions=  3.6e+07 Memory=   606.192 t=     84.4 R=   2e+05
Depth=    2494 States=  1.6e+07 Transitions= 3.84e+07 Memory=   638.616 t=     90.1 R=   2e+05
Depth=    2494 States=  1.7e+07 Transitions= 4.08e+07 Memory=   671.995 t=     95.7 R=   2e+05
Depth=    2494 States=  1.8e+07 Transitions= 4.32e+07 Memory=   703.943 t=      101 R=   2e+05
Depth=    2494 States=  1.9e+07 Transitions= 4.56e+07 Memory=   736.845 t=      107 R=   2e+05
Depth=    2494 States=    2e+07 Transitions= 4.81e+07 Memory=   769.747 t=      113 R=   2e+05
Depth=    2494 States=  2.1e+07 Transitions= 5.05e+07 Memory=   803.602 t=      119 R=   2e+05
Depth=    2494 States=  2.2e+07 Transitions= 5.29e+07 Memory=   836.504 t=      124 R=   2e+05
Depth=    2494 States=  2.3e+07 Transitions= 5.54e+07 Memory=   869.406 t=      130 R=   2e+05
Depth=    2494 States=  2.4e+07 Transitions= 5.78e+07 Memory=   903.261 t=      136 R=   2e+05
Depth=    2494 States=  2.5e+07 Transitions= 6.02e+07 Memory=   936.163 t=      142 R=   2e+05
Depth=    2494 States=  2.6e+07 Transitions= 6.26e+07 Memory=   970.972 t=      148 R=   2e+05
Depth=    2494 States=  2.7e+07 Transitions=  6.5e+07 Memory=  1004.827 t=      153 R=   2e+05
Depth=    2494 States=  2.8e+07 Transitions= 6.74e+07 Memory=  1038.206 t=      159 R=   2e+05
Depth=    2494 States=  2.9e+07 Transitions= 6.98e+07 Memory=  1071.108 t=      165 R=   2e+05
Depth=    2494 States=    3e+07 Transitions= 7.22e+07 Memory=  1102.579 t=      171 R=   2e+05
Depth=    2494 States=  3.1e+07 Transitions= 7.46e+07 Memory=  1135.004 t=      177 R=   2e+05
Depth=    2494 States=  3.2e+07 Transitions=  7.7e+07 Memory=  1166.952 t=      183 R=   2e+05
Depth=    2494 States=  3.3e+07 Transitions= 7.94e+07 Memory=  1199.854 t=      189 R=   2e+05
Depth=    2494 States=  3.4e+07 Transitions= 8.18e+07 Memory=  1231.325 t=      195 R=   2e+05
pan: resizing hashtable to -w26..  done
Depth=    2494 States=  3.5e+07 Transitions= 8.42e+07 Memory=  1763.352 t=      203 R=   2e+05
Depth=    2494 States=  3.6e+07 Transitions= 8.66e+07 Memory=  1798.161 t=      209 R=   2e+05
Depth=    2508 States=  3.7e+07 Transitions=  8.9e+07 Memory=  1833.447 t=      214 R=   2e+05
Depth=    2508 States=  3.8e+07 Transitions= 9.14e+07 Memory=  1869.210 t=      220 R=   2e+05
Depth=    2508 States=  3.9e+07 Transitions= 9.38e+07 Memory=  1903.066 t=      226 R=   2e+05
Depth=    2508 States=    4e+07 Transitions= 9.63e+07 Memory=  1936.444 t=      231 R=   2e+05
Depth=    2508 States=  4.1e+07 Transitions= 9.87e+07 Memory=  1970.300 t=      237 R=   2e+05
Depth=    2508 States=  4.2e+07 Transitions= 1.01e+08 Memory=  2004.155 t=      243 R=   2e+05
Depth=    2508 States=  4.3e+07 Transitions= 1.04e+08 Memory=  2039.441 t=      248 R=   2e+05
Depth=    2508 States=  4.4e+07 Transitions= 1.06e+08 Memory=  2073.296 t=      254 R=   2e+05
Depth=    2508 States=  4.5e+07 Transitions= 1.08e+08 Memory=  2107.152 t=      260 R=   2e+05
Depth=    2508 States=  4.6e+07 Transitions= 1.11e+08 Memory=  2141.484 t=      266 R=   2e+05
Depth=    2508 States=  4.7e+07 Transitions= 1.13e+08 Memory=  2176.770 t=      271 R=   2e+05
Depth=    2508 States=  4.8e+07 Transitions= 1.16e+08 Memory=  2210.625 t=      277 R=   2e+05
Depth=    2508 States=  4.9e+07 Transitions= 1.18e+08 Memory=  2245.911 t=      282 R=   2e+05
Depth=    2508 States=    5e+07 Transitions=  1.2e+08 Memory=  2277.860 t=      288 R=   2e+05
Depth=    2508 States=  5.1e+07 Transitions= 1.23e+08 Memory=  2309.808 t=      294 R=   2e+05
Depth=    2508 States=  5.2e+07 Transitions= 1.25e+08 Memory=  2342.233 t=      300 R=   2e+05
Depth=    2508 States=  5.3e+07 Transitions= 1.28e+08 Memory=  2377.042 t=      305 R=   2e+05
Depth=    2508 States=  5.4e+07 Transitions=  1.3e+08 Memory=  2411.851 t=      311 R=   2e+05
Depth=    2508 States=  5.5e+07 Transitions= 1.33e+08 Memory=  2447.137 t=      316 R=   2e+05
Depth=    2508 States=  5.6e+07 Transitions= 1.35e+08 Memory=  2481.469 t=      322 R=   2e+05
Depth=    2508 States=  5.7e+07 Transitions= 1.37e+08 Memory=  2515.324 t=      328 R=   2e+05
Depth=    2508 States=  5.8e+07 Transitions=  1.4e+08 Memory=  2549.657 t=      333 R=   2e+05
Depth=    2508 States=  5.9e+07 Transitions= 1.42e+08 Memory=  2583.512 t=      339 R=   2e+05
Depth=    2508 States=    6e+07 Transitions= 1.45e+08 Memory=  2617.844 t=      345 R=   2e+05
Depth=    2508 States=  6.1e+07 Transitions= 1.47e+08 Memory=  2652.654 t=      350 R=   2e+05
Depth=    2508 States=  6.2e+07 Transitions=  1.5e+08 Memory=  2685.078 t=      356 R=   2e+05
Depth=    2508 States=  6.3e+07 Transitions= 1.52e+08 Memory=  2719.411 t=      362 R=   2e+05
Depth=    2508 States=  6.4e+07 Transitions= 1.55e+08 Memory=  2755.650 t=      368 R=   2e+05
Depth=    2508 States=  6.5e+07 Transitions= 1.57e+08 Memory=  2791.413 t=      373 R=   2e+05
Depth=    2508 States=  6.6e+07 Transitions=  1.6e+08 Memory=  2826.222 t=      379 R=   2e+05
Depth=    2508 States=  6.7e+07 Transitions= 1.62e+08 Memory=  2860.078 t=      385 R=   2e+05
Depth=    2508 States=  6.8e+07 Transitions= 1.64e+08 Memory=  2894.410 t=      390 R=   2e+05
Depth=    2508 States=  6.9e+07 Transitions= 1.67e+08 Memory=  2930.650 t=      396 R=   2e+05
Depth=    2508 States=    7e+07 Transitions= 1.69e+08 Memory=  2965.459 t=      402 R=   2e+05
Depth=    2508 States=  7.1e+07 Transitions= 1.72e+08 Memory=  3000.268 t=      407 R=   2e+05
Depth=    2508 States=  7.2e+07 Transitions= 1.74e+08 Memory=  3035.077 t=      413 R=   2e+05
Depth=    2508 States=  7.3e+07 Transitions= 1.76e+08 Memory=  3067.025 t=      419 R=   2e+05
Depth=    2508 States=  7.4e+07 Transitions= 1.79e+08 Memory=  3101.357 t=      424 R=   2e+05
Depth=    2508 States=  7.5e+07 Transitions= 1.81e+08 Memory=  3134.736 t=      430 R=   2e+05
Depth=    2508 States=  7.6e+07 Transitions= 1.84e+08 Memory=  3172.406 t=      436 R=   2e+05
Depth=    2508 States=  7.7e+07 Transitions= 1.86e+08 Memory=  3207.215 t=      442 R=   2e+05
Depth=    2508 States=  7.8e+07 Transitions= 1.89e+08 Memory=  3241.071 t=      448 R=   2e+05
Depth=    2508 States=  7.9e+07 Transitions= 1.91e+08 Memory=  3276.357 t=      453 R=   2e+05
Depth=    2508 States=    8e+07 Transitions= 1.93e+08 Memory=  3310.212 t=      459 R=   2e+05
Depth=    2508 States=  8.1e+07 Transitions= 1.96e+08 Memory=  3344.067 t=      465 R=   2e+05
Depth=    2508 States=  8.2e+07 Transitions= 1.98e+08 Memory=  3377.923 t=      471 R=   2e+05
Depth=    2508 States=  8.3e+07 Transitions= 2.01e+08 Memory=  3409.871 t=      477 R=   2e+05
Depth=    2508 States=  8.4e+07 Transitions= 2.03e+08 Memory=  3442.296 t=      482 R=   2e+05
Depth=    2508 States=  8.5e+07 Transitions= 2.05e+08 Memory=  3473.767 t=      488 R=   2e+05
Depth=    2508 States=  8.6e+07 Transitions= 2.08e+08 Memory=  3507.623 t=      494 R=   2e+05
Depth=    2508 States=  8.7e+07 Transitions=  2.1e+08 Memory=  3542.909 t=      500 R=   2e+05
Depth=    2508 States=  8.8e+07 Transitions= 2.13e+08 Memory=  3577.718 t=      506 R=   2e+05
Depth=    2508 States=  8.9e+07 Transitions= 2.15e+08 Memory=  3611.096 t=      511 R=   2e+05
Depth=    2508 States=    9e+07 Transitions= 2.18e+08 Memory=  3644.475 t=      517 R=   2e+05
Depth=    2508 States=  9.1e+07 Transitions=  2.2e+08 Memory=  3677.377 t=      523 R=   2e+05
Depth=    2508 States=  9.2e+07 Transitions= 2.22e+08 Memory=  3712.186 t=      529 R=   2e+05
Depth=    2508 States=  9.3e+07 Transitions= 2.25e+08 Memory=  3745.564 t=      534 R=   2e+05
Depth=    2508 States=  9.4e+07 Transitions= 2.27e+08 Memory=  3778.943 t=      540 R=   2e+05
Depth=    2508 States=  9.5e+07 Transitions=  2.3e+08 Memory=  3811.368 t=      546 R=   2e+05
Depth=    2508 States=  9.6e+07 Transitions= 2.32e+08 Memory=  3845.700 t=      551 R=   2e+05
Depth=    2508 States=  9.7e+07 Transitions= 2.34e+08 Memory=  3881.463 t=      557 R=   2e+05
Depth=    2508 States=  9.8e+07 Transitions= 2.37e+08 Memory=  3914.365 t=      563 R=   2e+05
Depth=    2508 States=  9.9e+07 Transitions= 2.39e+08 Memory=  3947.743 t=      568 R=   2e+05
Depth=    2508 States=    1e+08 Transitions= 2.42e+08 Memory=  3980.168 t=      574 R=   2e+05
Depth=    2508 States= 1.01e+08 Transitions= 2.44e+08 Memory=  4013.547 t=      580 R=   2e+05
Depth=    2508 States= 1.02e+08 Transitions= 2.46e+08 Memory=  4046.925 t=      585 R=   2e+05
Depth=    2508 States= 1.03e+08 Transitions= 2.49e+08 Memory=  4079.827 t=      591 R=   2e+05
Depth=    2508 States= 1.04e+08 Transitions= 2.51e+08 Memory=  4114.159 t=      597 R=   2e+05
Depth=    2508 States= 1.05e+08 Transitions= 2.54e+08 Memory=  4147.538 t=      602 R=   2e+05
Depth=    2508 States= 1.06e+08 Transitions= 2.56e+08 Memory=  4180.440 t=      608 R=   2e+05
Depth=    2508 States= 1.07e+08 Transitions= 2.59e+08 Memory=  4213.818 t=      614 R=   2e+05
Depth=    2508 States= 1.08e+08 Transitions= 2.61e+08 Memory=  4247.197 t=      620 R=   2e+05
Depth=    2508 States= 1.09e+08 Transitions= 2.63e+08 Memory=  4281.052 t=      625 R=   2e+05
Depth=    2508 States=  1.1e+08 Transitions= 2.66e+08 Memory=  4314.431 t=      631 R=   2e+05
Depth=    2508 States= 1.11e+08 Transitions= 2.68e+08 Memory=  4347.810 t=      637 R=   2e+05
Depth=    2508 States= 1.12e+08 Transitions= 2.71e+08 Memory=  4382.142 t=      643 R=   2e+05
Depth=    2508 States= 1.13e+08 Transitions= 2.73e+08 Memory=  4415.997 t=      649 R=   2e+05
Depth=    2508 States= 1.14e+08 Transitions= 2.75e+08 Memory=  4447.469 t=      654 R=   2e+05
Depth=    2508 States= 1.15e+08 Transitions= 2.78e+08 Memory=  4478.940 t=      660 R=   2e+05
Depth=    2508 States= 1.16e+08 Transitions=  2.8e+08 Memory=  4509.934 t=      666 R=   2e+05
Depth=    2508 States= 1.17e+08 Transitions= 2.83e+08 Memory=  4540.452 t=      672 R=   2e+05
Depth=    2508 States= 1.18e+08 Transitions= 2.85e+08 Memory=  4571.923 t=      678 R=   2e+05
Depth=    2508 States= 1.19e+08 Transitions= 2.88e+08 Memory=  4602.918 t=      684 R=   2e+05
Depth=    2508 States=  1.2e+08 Transitions=  2.9e+08 Memory=  4634.389 t=      689 R=   2e+05
Depth=    2508 States= 1.21e+08 Transitions= 2.92e+08 Memory=  4665.860 t=      695 R=   2e+05
Depth=    2508 States= 1.22e+08 Transitions= 2.95e+08 Memory=  4698.762 t=      701 R=   2e+05
Depth=    2508 States= 1.23e+08 Transitions= 2.97e+08 Memory=  4731.664 t=      707 R=   2e+05
Depth=    2508 States= 1.24e+08 Transitions=    3e+08 Memory=  4763.135 t=      712 R=   2e+05
Depth=    2508 States= 1.25e+08 Transitions= 3.02e+08 Memory=  4794.606 t=      718 R=   2e+05
Depth=    2508 States= 1.26e+08 Transitions= 3.04e+08 Memory=  4825.600 t=      724 R=   2e+05
Depth=    2508 States= 1.27e+08 Transitions= 3.07e+08 Memory=  4857.072 t=      729 R=   2e+05
Depth=    2508 States= 1.28e+08 Transitions= 3.09e+08 Memory=  4888.066 t=      735 R=   2e+05
Depth=    2508 States= 1.29e+08 Transitions= 3.12e+08 Memory=  4920.014 t=      741 R=   2e+05
Depth=    2508 States=  1.3e+08 Transitions= 3.14e+08 Memory=  4952.916 t=      747 R=   2e+05
Depth=    2508 States= 1.31e+08 Transitions= 3.16e+08 Memory=  4986.771 t=      752 R=   2e+05
Depth=    2508 States= 1.32e+08 Transitions= 3.19e+08 Memory=  5020.627 t=      758 R=   2e+05
Depth=    2508 States= 1.33e+08 Transitions= 3.21e+08 Memory=  5054.005 t=      764 R=   2e+05
Depth=    2508 States= 1.34e+08 Transitions= 3.24e+08 Memory=  5087.384 t=      770 R=   2e+05
Depth=    2508 States= 1.35e+08 Transitions= 3.26e+08 Memory=  5121.240 t=      775 R=   2e+05
pan: resizing hashtable to -w28..  done
Depth=    2508 States= 1.36e+08 Transitions= 3.29e+08 Memory=  7169.240 t=      794 R=   2e+05
Depth=    2508 States= 1.37e+08 Transitions= 3.31e+08 Memory=  7173.054 t=      800 R=   2e+05
Depth=    2508 States= 1.38e+08 Transitions= 3.33e+08 Memory=  7204.525 t=      805 R=   2e+05
Depth=    2508 States= 1.39e+08 Transitions= 3.36e+08 Memory=  7236.950 t=      811 R=   2e+05
Depth=    2508 States=  1.4e+08 Transitions= 3.38e+08 Memory=  7267.945 t=      817 R=   2e+05
Depth=    2508 States= 1.41e+08 Transitions= 3.41e+08 Memory=  7302.277 t=      822 R=   2e+05
Depth=    2508 States= 1.42e+08 Transitions= 3.43e+08 Memory=  7336.609 t=      828 R=   2e+05
Depth=    2508 States= 1.43e+08 Transitions= 3.46e+08 Memory=  7369.034 t=      834 R=   2e+05
Depth=    2508 States= 1.44e+08 Transitions= 3.48e+08 Memory=  7402.413 t=      840 R=   2e+05
Depth=    2508 States= 1.45e+08 Transitions=  3.5e+08 Memory=  7433.884 t=      845 R=   2e+05
Depth=    2508 States= 1.46e+08 Transitions= 3.53e+08 Memory=  7466.309 t=      851 R=   2e+05
Depth=    2508 States= 1.47e+08 Transitions= 3.55e+08 Memory=  7500.164 t=      856 R=   2e+05
Depth=    2508 States= 1.48e+08 Transitions= 3.58e+08 Memory=  7532.589 t=      862 R=   2e+05
Depth=    2508 States= 1.49e+08 Transitions=  3.6e+08 Memory=  7565.491 t=      868 R=   2e+05
Depth=    2508 States=  1.5e+08 Transitions= 3.62e+08 Memory=  7598.393 t=      873 R=   2e+05
Depth=    2508 States= 1.51e+08 Transitions= 3.65e+08 Memory=  7631.772 t=      879 R=   2e+05
Depth=    2508 States= 1.52e+08 Transitions= 3.67e+08 Memory=  7664.673 t=      885 R=   2e+05
Depth=    2508 States= 1.53e+08 Transitions=  3.7e+08 Memory=  7695.668 t=      890 R=   2e+05
Depth=    2508 States= 1.54e+08 Transitions= 3.72e+08 Memory=  7726.662 t=      896 R=   2e+05
Depth=    2508 States= 1.55e+08 Transitions= 3.74e+08 Memory=  7758.610 t=      901 R=   2e+05
Depth=    2508 States= 1.56e+08 Transitions= 3.77e+08 Memory=  7790.558 t=      907 R=   2e+05
Depth=    2508 States= 1.57e+08 Transitions= 3.79e+08 Memory=  7827.275 t=      913 R=   2e+05
Depth=    2508 States= 1.58e+08 Transitions= 3.82e+08 Memory=  7861.607 t=      918 R=   2e+05
Depth=    2508 States= 1.59e+08 Transitions= 3.84e+08 Memory=  7894.986 t=      924 R=   2e+05
Depth=    2508 States=  1.6e+08 Transitions= 3.87e+08 Memory=  7929.318 t=      930 R=   2e+05
Depth=    2508 States= 1.61e+08 Transitions= 3.89e+08 Memory=  7962.697 t=      935 R=   2e+05
Depth=    2508 States= 1.62e+08 Transitions= 3.91e+08 Memory=  7996.552 t=      941 R=   2e+05
Depth=    2508 States= 1.63e+08 Transitions= 3.94e+08 Memory=  8028.977 t=      946 R=   2e+05
Depth=    2508 States= 1.64e+08 Transitions= 3.96e+08 Memory=  8064.263 t=      952 R=   2e+05
Depth=    2508 States= 1.65e+08 Transitions= 3.99e+08 Memory=  8096.211 t=      958 R=   2e+05
Depth=    2508 States= 1.66e+08 Transitions= 4.01e+08 Memory=  8127.682 t=      963 R=   2e+05
Depth=    2508 States= 1.67e+08 Transitions= 4.03e+08 Memory=  8158.200 t=      969 R=   2e+05
Depth=    2508 States= 1.68e+08 Transitions= 4.06e+08 Memory=  8189.194 t=      975 R=   2e+05
Depth=    2508 States= 1.69e+08 Transitions= 4.08e+08 Memory=  8220.189 t=      980 R=   2e+05
Depth=    2508 States=  1.7e+08 Transitions= 4.11e+08 Memory=  8251.660 t=      986 R=   2e+05
Depth=    2508 States= 1.71e+08 Transitions= 4.13e+08 Memory=  8287.423 t=      992 R=   2e+05
Depth=    2508 States= 1.72e+08 Transitions= 4.16e+08 Memory=  8334.153 t=      998 R=   2e+05
Depth=    2530 States= 1.73e+08 Transitions= 4.19e+08 Memory=  8399.003 t=    1e+03 R=   2e+05
Depth=    2538 States= 1.74e+08 Transitions= 4.21e+08 Memory=  8463.852 t= 1.01e+03 R=   2e+05
Depth=    2538 States= 1.75e+08 Transitions= 4.24e+08 Memory=  8526.318 t= 1.02e+03 R=   2e+05
Depth=    2538 States= 1.76e+08 Transitions= 4.27e+08 Memory=  8589.261 t= 1.03e+03 R=   2e+05
Depth=    2538 States= 1.77e+08 Transitions=  4.3e+08 Memory=  8652.203 t= 1.03e+03 R=   2e+05
Depth=    2538 States= 1.78e+08 Transitions= 4.33e+08 Memory=  8714.192 t= 1.04e+03 R=   2e+05
Depth=    2538 States= 1.79e+08 Transitions= 4.36e+08 Memory=  8776.658 t= 1.05e+03 R=   2e+05
Depth=    2538 States=  1.8e+08 Transitions= 4.39e+08 Memory=  8838.646 t= 1.05e+03 R=   2e+05
Depth=    2538 States= 1.81e+08 Transitions= 4.42e+08 Memory=  8900.635 t= 1.06e+03 R=   2e+05
Depth=    2538 States= 1.82e+08 Transitions= 4.44e+08 Memory=  8968.346 t= 1.07e+03 R=   2e+05
Depth=    2538 States= 1.83e+08 Transitions= 4.47e+08 Memory=  9034.626 t= 1.07e+03 R=   2e+05
Depth=    2538 States= 1.84e+08 Transitions=  4.5e+08 Memory=  9101.384 t= 1.08e+03 R=   2e+05
Depth=    2538 States= 1.85e+08 Transitions= 4.52e+08 Memory=  9167.664 t= 1.09e+03 R=   2e+05
Depth=    2538 States= 1.86e+08 Transitions= 4.55e+08 Memory=  9233.944 t= 1.09e+03 R=   2e+05
Depth=    2538 States= 1.87e+08 Transitions= 4.58e+08 Memory=  9302.609 t=  1.1e+03 R=   2e+05
Depth=    2538 States= 1.88e+08 Transitions= 4.61e+08 Memory=  9368.412 t= 1.11e+03 R=   2e+05
Depth=    2538 States= 1.89e+08 Transitions= 4.64e+08 Memory=  9435.170 t= 1.12e+03 R=   2e+05
Depth=    2538 States=  1.9e+08 Transitions= 4.67e+08 Memory=  9500.020 t= 1.12e+03 R=   2e+05
Depth=    2538 States= 1.91e+08 Transitions=  4.7e+08 Memory=  9566.300 t= 1.13e+03 R=   2e+05
Depth=    2538 States= 1.92e+08 Transitions= 4.73e+08 Memory=  9633.057 t= 1.14e+03 R=   2e+05
Depth=    2538 States= 1.93e+08 Transitions= 4.76e+08 Memory=  9701.245 t= 1.15e+03 R=   2e+05
Depth=    2538 States= 1.94e+08 Transitions= 4.79e+08 Memory=  9766.572 t= 1.15e+03 R=   2e+05
Depth=    2538 States= 1.95e+08 Transitions= 4.82e+08 Memory=  9831.898 t= 1.16e+03 R=   2e+05
Depth=    2538 States= 1.96e+08 Transitions= 4.84e+08 Memory=  9897.702 t= 1.17e+03 R=   2e+05
Depth=    2538 States= 1.97e+08 Transitions= 4.87e+08 Memory=  9962.075 t= 1.17e+03 R=   2e+05
Depth=    2538 States= 1.98e+08 Transitions=  4.9e+08 Memory= 10026.925 t= 1.18e+03 R=   2e+05
Depth=    2538 States= 1.99e+08 Transitions= 4.93e+08 Memory= 10097.496 t= 1.19e+03 R=   2e+05
Depth=    2552 States=    2e+08 Transitions= 4.96e+08 Memory= 10167.115 t=  1.2e+03 R=   2e+05
Depth=    2552 States= 2.01e+08 Transitions= 4.99e+08 Memory= 10235.302 t=  1.2e+03 R=   2e+05
Depth=    2552 States= 2.02e+08 Transitions= 5.01e+08 Memory= 10303.967 t= 1.21e+03 R=   2e+05
Depth=    2552 States= 2.03e+08 Transitions= 5.04e+08 Memory= 10371.678 t= 1.22e+03 R=   2e+05
Depth=    2552 States= 2.04e+08 Transitions= 5.07e+08 Memory= 10439.866 t= 1.22e+03 R=   2e+05
Depth=    2552 States= 2.05e+08 Transitions=  5.1e+08 Memory= 10508.053 t= 1.23e+03 R=   2e+05
Depth=    2552 States= 2.06e+08 Transitions= 5.12e+08 Memory= 10575.764 t= 1.24e+03 R=   2e+05
Depth=    2552 States= 2.07e+08 Transitions= 5.15e+08 Memory= 10641.568 t= 1.24e+03 R=   2e+05
Depth=    2552 States= 2.08e+08 Transitions= 5.18e+08 Memory= 10709.279 t= 1.25e+03 R=   2e+05
Depth=    2552 States= 2.09e+08 Transitions= 5.22e+08 Memory= 10773.175 t= 1.26e+03 R=   2e+05
Depth=    2552 States=  2.1e+08 Transitions= 5.26e+08 Memory= 10837.548 t= 1.27e+03 R=   2e+05
Depth=    2552 States= 2.11e+08 Transitions=  5.3e+08 Memory= 10903.828 t= 1.28e+03 R=   2e+05
Depth=    2552 States= 2.12e+08 Transitions= 5.34e+08 Memory= 10971.539 t= 1.29e+03 R=   2e+05
Depth=    2552 States= 2.13e+08 Transitions= 5.38e+08 Memory= 11036.389 t=  1.3e+03 R=   2e+05
Depth=    2552 States= 2.14e+08 Transitions= 5.42e+08 Memory= 11101.716 t= 1.31e+03 R=   2e+05
Depth=    2552 States= 2.15e+08 Transitions= 5.46e+08 Memory= 11167.996 t= 1.32e+03 R=   2e+05
Depth=    2552 States= 2.16e+08 Transitions=  5.5e+08 Memory= 11235.707 t= 1.33e+03 R=   2e+05
Depth=    2552 States= 2.17e+08 Transitions= 5.54e+08 Memory= 11302.464 t= 1.34e+03 R=   2e+05
Depth=    2552 States= 2.18e+08 Transitions= 5.56e+08 Memory= 11370.175 t= 1.34e+03 R=   2e+05
Depth=    2552 States= 2.19e+08 Transitions= 5.59e+08 Memory= 11439.793 t= 1.35e+03 R=   2e+05
Depth=    2552 States=  2.2e+08 Transitions= 5.62e+08 Memory= 11505.597 t= 1.36e+03 R=   2e+05
Depth=    2552 States= 2.21e+08 Transitions= 5.64e+08 Memory= 11569.493 t= 1.36e+03 R=   2e+05
Depth=    2552 States= 2.22e+08 Transitions= 5.67e+08 Memory= 11637.204 t= 1.37e+03 R=   2e+05
Depth=    2552 States= 2.23e+08 Transitions= 5.71e+08 Memory= 11703.007 t= 1.38e+03 R=   2e+05
Depth=    2552 States= 2.24e+08 Transitions= 5.75e+08 Memory= 11766.427 t= 1.39e+03 R=   2e+05
Depth=    2552 States= 2.25e+08 Transitions= 5.78e+08 Memory= 11832.230 t=  1.4e+03 R=   2e+05
Depth=    2552 States= 2.26e+08 Transitions= 5.81e+08 Memory= 11894.696 t=  1.4e+03 R=   2e+05
Depth=    2552 States= 2.27e+08 Transitions= 5.84e+08 Memory= 11959.546 t= 1.41e+03 R=   2e+05
Depth=    2552 States= 2.28e+08 Transitions= 5.87e+08 Memory= 12023.442 t= 1.42e+03 R=   2e+05
Depth=    2552 States= 2.29e+08 Transitions=  5.9e+08 Memory= 12092.583 t= 1.43e+03 R=   2e+05
Depth=    2552 States=  2.3e+08 Transitions= 5.93e+08 Memory= 12159.817 t= 1.43e+03 R=   2e+05
Depth=    2552 States= 2.31e+08 Transitions= 5.96e+08 Memory= 12225.144 t= 1.44e+03 R=   2e+05
Depth=    2552 States= 2.32e+08 Transitions= 5.99e+08 Memory= 12290.947 t= 1.45e+03 R=   2e+05
Depth=    2552 States= 2.33e+08 Transitions= 6.01e+08 Memory= 12358.181 t= 1.46e+03 R=   2e+05
Depth=    2552 States= 2.34e+08 Transitions= 6.05e+08 Memory= 12421.601 t= 1.46e+03 R=   2e+05
Depth=    2552 States= 2.35e+08 Transitions= 6.07e+08 Memory= 12486.451 t= 1.47e+03 R=   2e+05
Depth=    2552 States= 2.36e+08 Transitions= 6.11e+08 Memory= 12550.347 t= 1.48e+03 R=   2e+05
Depth=    2552 States= 2.37e+08 Transitions= 6.13e+08 Memory= 12617.104 t= 1.49e+03 R=   2e+05
Depth=    2552 States= 2.38e+08 Transitions= 6.16e+08 Memory= 12681.477 t= 1.49e+03 R=   2e+05
Depth=    2552 States= 2.39e+08 Transitions= 6.19e+08 Memory= 12747.757 t=  1.5e+03 R=   2e+05
Depth=    2552 States=  2.4e+08 Transitions= 6.22e+08 Memory= 12812.130 t= 1.51e+03 R=   2e+05
Depth=    2552 States= 2.41e+08 Transitions= 6.25e+08 Memory= 12876.503 t= 1.51e+03 R=   2e+05
Depth=    2552 States= 2.42e+08 Transitions= 6.29e+08 Memory= 12939.446 t= 1.52e+03 R=   2e+05
Depth=    2552 States= 2.43e+08 Transitions= 6.32e+08 Memory= 13006.203 t= 1.53e+03 R=   2e+05
Depth=    2552 States= 2.44e+08 Transitions= 6.35e+08 Memory= 13073.437 t= 1.54e+03 R=   2e+05
Depth=    2552 States= 2.45e+08 Transitions= 6.38e+08 Memory= 13138.764 t= 1.55e+03 R=   2e+05
Depth=    2552 States= 2.46e+08 Transitions= 6.41e+08 Memory= 13203.137 t= 1.55e+03 R=   2e+05
Depth=    2552 States= 2.47e+08 Transitions= 6.44e+08 Memory= 13266.079 t= 1.56e+03 R=   2e+05
Depth=    2552 States= 2.48e+08 Transitions= 6.47e+08 Memory= 13328.545 t= 1.57e+03 R=   2e+05
Depth=    2552 States= 2.49e+08 Transitions=  6.5e+08 Memory= 13391.964 t= 1.58e+03 R=   2e+05
Depth=    2552 States=  2.5e+08 Transitions= 6.53e+08 Memory= 13453.953 t= 1.58e+03 R=   2e+05
Depth=    2552 States= 2.51e+08 Transitions= 6.56e+08 Memory= 13506.882 t= 1.59e+03 R=   2e+05
Depth=    2552 States= 2.52e+08 Transitions= 6.59e+08 Memory= 13571.255 t=  1.6e+03 R=   2e+05
Depth=    2552 States= 2.53e+08 Transitions= 6.62e+08 Memory= 13634.198 t= 1.61e+03 R=   2e+05
Depth=    2552 States= 2.54e+08 Transitions= 6.64e+08 Memory= 13699.048 t= 1.61e+03 R=   2e+05
Depth=    2552 States= 2.55e+08 Transitions= 6.67e+08 Memory= 13761.513 t= 1.62e+03 R=   2e+05
Depth=    2552 States= 2.56e+08 Transitions=  6.7e+08 Memory= 13824.456 t= 1.63e+03 R=   2e+05
Depth=    2552 States= 2.57e+08 Transitions= 6.73e+08 Memory= 13888.829 t= 1.63e+03 R=   2e+05
Depth=    2552 States= 2.58e+08 Transitions= 6.76e+08 Memory= 13952.248 t= 1.64e+03 R=   2e+05
Depth=    2552 States= 2.59e+08 Transitions=  6.8e+08 Memory= 14015.667 t= 1.65e+03 R=   2e+05
Depth=    2552 States=  2.6e+08 Transitions= 6.83e+08 Memory= 14080.517 t= 1.66e+03 R=   2e+05
Depth=    2552 States= 2.61e+08 Transitions= 6.86e+08 Memory= 14143.460 t= 1.67e+03 R=   2e+05
Depth=    2552 States= 2.62e+08 Transitions= 6.89e+08 Memory= 14206.879 t= 1.67e+03 R=   2e+05
Depth=    2552 States= 2.63e+08 Transitions= 6.92e+08 Memory= 14271.729 t= 1.68e+03 R=   2e+05
Depth=    2552 States= 2.64e+08 Transitions= 6.95e+08 Memory= 14337.533 t= 1.69e+03 R=   2e+05
Depth=    2552 States= 2.65e+08 Transitions= 6.98e+08 Memory= 14400.952 t=  1.7e+03 R=   2e+05
Depth=    2552 States= 2.66e+08 Transitions= 7.01e+08 Memory= 14467.709 t=  1.7e+03 R=   2e+05
Depth=    2552 States= 2.67e+08 Transitions= 7.04e+08 Memory= 14531.605 t= 1.71e+03 R=   2e+05
Depth=    2552 States= 2.68e+08 Transitions= 7.07e+08 Memory= 14594.548 t= 1.72e+03 R=   2e+05
Depth=    2552 States= 2.69e+08 Transitions=  7.1e+08 Memory= 14658.444 t= 1.73e+03 R=   2e+05
Depth=    2552 States=  2.7e+08 Transitions= 7.13e+08 Memory= 14720.433 t= 1.73e+03 R=   2e+05
Depth=    2552 States= 2.71e+08 Transitions= 7.16e+08 Memory= 14786.236 t= 1.74e+03 R=   2e+05
Depth=    2552 States= 2.72e+08 Transitions= 7.18e+08 Memory= 14852.517 t= 1.75e+03 R=   2e+05
Depth=    2552 States= 2.73e+08 Transitions= 7.21e+08 Memory= 14914.982 t= 1.76e+03 R=   2e+05
Depth=    2552 States= 2.74e+08 Transitions= 7.24e+08 Memory= 14977.925 t= 1.76e+03 R=   2e+05
Depth=    2552 States= 2.75e+08 Transitions= 7.27e+08 Memory= 15042.775 t= 1.77e+03 R=   2e+05
Depth=    2552 States= 2.76e+08 Transitions= 7.31e+08 Memory= 15108.101 t= 1.78e+03 R=   2e+05
Depth=    2552 States= 2.77e+08 Transitions= 7.34e+08 Memory= 15172.474 t= 1.79e+03 R=   2e+05
Depth=    2552 States= 2.78e+08 Transitions= 7.37e+08 Memory= 15237.801 t= 1.79e+03 R=   2e+05
Depth=    2552 States= 2.79e+08 Transitions=  7.4e+08 Memory= 15303.128 t=  1.8e+03 R=   2e+05
Depth=    2552 States=  2.8e+08 Transitions= 7.43e+08 Memory= 15367.024 t= 1.81e+03 R=   2e+05
Depth=    2552 States= 2.81e+08 Transitions= 7.46e+08 Memory= 15429.966 t= 1.82e+03 R=   2e+05
Depth=    2552 States= 2.82e+08 Transitions= 7.49e+08 Memory= 15491.955 t= 1.83e+03 R=   2e+05
Depth=    2552 States= 2.83e+08 Transitions= 7.52e+08 Memory= 15549.653 t= 1.83e+03 R=   2e+05
Depth=    2552 States= 2.84e+08 Transitions= 7.55e+08 Memory= 15597.813 t= 1.84e+03 R=   2e+05
Depth=    2552 States= 2.85e+08 Transitions= 7.59e+08 Memory= 15658.848 t= 1.85e+03 R=   2e+05
Depth=    2552 States= 2.86e+08 Transitions= 7.63e+08 Memory= 15720.837 t= 1.86e+03 R=   2e+05
Depth=    2552 States= 2.87e+08 Transitions= 7.67e+08 Memory= 15785.687 t= 1.87e+03 R=   2e+05
Depth=    2552 States= 2.88e+08 Transitions= 7.71e+08 Memory= 15848.629 t= 1.88e+03 R=   2e+05
Depth=    2552 States= 2.89e+08 Transitions= 7.75e+08 Memory= 15911.095 t= 1.89e+03 R=   2e+05
Depth=    2552 States=  2.9e+08 Transitions= 7.79e+08 Memory= 15977.852 t=  1.9e+03 R=   2e+05
Depth=    2552 States= 2.91e+08 Transitions= 7.83e+08 Memory= 16041.272 t= 1.91e+03 R=   2e+05
Depth=    2552 States= 2.92e+08 Transitions= 7.87e+08 Memory= 16104.214 t= 1.92e+03 R=   2e+05
Depth=    2552 States= 2.93e+08 Transitions= 7.91e+08 Memory= 16169.541 t= 1.93e+03 R=   2e+05
Depth=    2552 States= 2.94e+08 Transitions= 7.95e+08 Memory= 16231.530 t= 1.94e+03 R=   2e+05
Depth=    2552 States= 2.95e+08 Transitions= 7.99e+08 Memory= 16293.042 t= 1.95e+03 R=   2e+05
Depth=    2552 States= 2.96e+08 Transitions= 8.03e+08 Memory= 16355.031 t= 1.96e+03 R=   2e+05
Depth=    2552 States= 2.97e+08 Transitions= 8.07e+08 Memory= 16416.543 t= 1.97e+03 R=   2e+05
Depth=    2552 States= 2.98e+08 Transitions= 8.11e+08 Memory= 16478.055 t= 1.98e+03 R=   2e+05
Depth=    2552 States= 2.99e+08 Transitions= 8.15e+08 Memory= 16540.520 t= 1.99e+03 R=   2e+05
Depth=    2552 States=    3e+08 Transitions= 8.19e+08 Memory= 16602.032 t=    2e+03 R=   2e+05
Depth=    2552 States= 3.01e+08 Transitions= 8.22e+08 Memory= 16663.544 t= 2.01e+03 R=   1e+05
Depth=    2552 States= 3.02e+08 Transitions= 8.26e+08 Memory= 16725.056 t= 2.02e+03 R=   1e+05
Depth=    2552 States= 3.03e+08 Transitions=  8.3e+08 Memory= 16786.568 t= 2.03e+03 R=   1e+05
Depth=    2552 States= 3.04e+08 Transitions= 8.34e+08 Memory= 16847.603 t= 2.04e+03 R=   1e+05
Depth=    2552 States= 3.05e+08 Transitions= 8.38e+08 Memory= 16909.592 t= 2.05e+03 R=   1e+05
Depth=    2552 States= 3.06e+08 Transitions= 8.42e+08 Memory= 16972.058 t= 2.06e+03 R=   1e+05
Depth=    2552 States= 3.07e+08 Transitions= 8.46e+08 Memory= 17033.570 t= 2.07e+03 R=   1e+05
Depth=    2552 States= 3.08e+08 Transitions=  8.5e+08 Memory= 17094.605 t= 2.08e+03 R=   1e+05
Depth=    2552 States= 3.09e+08 Transitions= 8.53e+08 Memory= 17138.474 t= 2.08e+03 R=   1e+05
Depth=    2552 States=  3.1e+08 Transitions= 8.55e+08 Memory= 17172.806 t= 2.09e+03 R=   1e+05
Depth=    2552 States= 3.11e+08 Transitions= 8.58e+08 Memory= 17206.185 t=  2.1e+03 R=   1e+05
Depth=    2552 States= 3.12e+08 Transitions=  8.6e+08 Memory= 17240.040 t=  2.1e+03 R=   1e+05
Depth=    2552 States= 3.13e+08 Transitions= 8.63e+08 Memory= 17272.465 t= 2.11e+03 R=   1e+05
Depth=    2552 States= 3.14e+08 Transitions= 8.65e+08 Memory= 17304.890 t= 2.11e+03 R=   1e+05
Depth=    2552 States= 3.15e+08 Transitions= 8.67e+08 Memory= 17337.792 t= 2.12e+03 R=   1e+05
Depth=    2552 States= 3.16e+08 Transitions=  8.7e+08 Memory= 17370.217 t= 2.13e+03 R=   1e+05
Depth=    2552 States= 3.17e+08 Transitions= 8.72e+08 Memory= 17402.642 t= 2.13e+03 R=   1e+05
Depth=    2552 States= 3.18e+08 Transitions= 8.75e+08 Memory= 17435.067 t= 2.14e+03 R=   1e+05
Depth=    2552 States= 3.19e+08 Transitions= 8.77e+08 Memory= 17467.015 t= 2.14e+03 R=   1e+05
Depth=    2552 States=  3.2e+08 Transitions= 8.79e+08 Memory= 17499.440 t= 2.15e+03 R=   1e+05
Depth=    2552 States= 3.21e+08 Transitions= 8.82e+08 Memory= 17536.156 t= 2.15e+03 R=   1e+05
Depth=    2552 States= 3.22e+08 Transitions= 8.84e+08 Memory= 17571.442 t= 2.16e+03 R=   1e+05
Depth=    2552 States= 3.23e+08 Transitions= 8.87e+08 Memory= 17606.251 t= 2.17e+03 R=   1e+05
Depth=    2552 States= 3.24e+08 Transitions= 8.89e+08 Memory= 17642.014 t= 2.17e+03 R=   1e+05
Depth=    2552 States= 3.25e+08 Transitions= 8.91e+08 Memory= 17676.823 t= 2.18e+03 R=   1e+05
Depth=    2552 States= 3.26e+08 Transitions= 8.94e+08 Memory= 17710.679 t= 2.18e+03 R=   1e+05
Depth=    2552 States= 3.27e+08 Transitions= 8.96e+08 Memory= 17745.011 t= 2.19e+03 R=   1e+05
Depth=    2552 States= 3.28e+08 Transitions= 8.99e+08 Memory= 17779.343 t=  2.2e+03 R=   1e+05
Depth=    2552 States= 3.29e+08 Transitions= 9.01e+08 Memory= 17813.675 t=  2.2e+03 R=   1e+05
Depth=    2552 States=  3.3e+08 Transitions= 9.04e+08 Memory= 17848.961 t= 2.21e+03 R=   1e+05
Depth=    2552 States= 3.31e+08 Transitions= 9.06e+08 Memory= 17883.770 t= 2.21e+03 R=   1e+05
Depth=    2552 States= 3.32e+08 Transitions= 9.08e+08 Memory= 17918.103 t= 2.22e+03 R=   1e+05
Depth=    2552 States= 3.33e+08 Transitions= 9.11e+08 Memory= 17953.389 t= 2.22e+03 R=   1e+05
Depth=    2552 States= 3.34e+08 Transitions= 9.13e+08 Memory= 17989.628 t= 2.23e+03 R=   1e+05
Depth=    2552 States= 3.35e+08 Transitions= 9.16e+08 Memory= 18024.914 t= 2.24e+03 R=   1e+05
Depth=    2552 States= 3.36e+08 Transitions= 9.18e+08 Memory= 18060.200 t= 2.24e+03 R=   1e+05
Depth=    2552 States= 3.37e+08 Transitions=  9.2e+08 Memory= 18094.532 t= 2.25e+03 R=   1e+05
Depth=    2552 States= 3.38e+08 Transitions= 9.23e+08 Memory= 18129.342 t= 2.25e+03 R=   1e+05
Depth=    2552 States= 3.39e+08 Transitions= 9.25e+08 Memory= 18163.674 t= 2.26e+03 R=   2e+05
Depth=    2552 States=  3.4e+08 Transitions= 9.28e+08 Memory= 18198.960 t= 2.27e+03 R=   2e+05
Depth=    2552 States= 3.41e+08 Transitions=  9.3e+08 Memory= 18233.769 t= 2.27e+03 R=   2e+05
Depth=    2552 States= 3.42e+08 Transitions= 9.32e+08 Memory= 18268.578 t= 2.28e+03 R=   2e+05
Depth=    2552 States= 3.43e+08 Transitions= 9.35e+08 Memory= 18304.818 t= 2.28e+03 R=   2e+05
Depth=    2552 States= 3.44e+08 Transitions= 9.37e+08 Memory= 18340.104 t= 2.29e+03 R=   2e+05
Depth=    2552 States= 3.45e+08 Transitions=  9.4e+08 Memory= 18374.913 t= 2.29e+03 R=   2e+05
Depth=    2552 States= 3.46e+08 Transitions= 9.42e+08 Memory= 18410.676 t=  2.3e+03 R=   2e+05
Depth=    2552 States= 3.47e+08 Transitions= 9.44e+08 Memory= 18445.008 t= 2.31e+03 R=   2e+05
Depth=    2552 States= 3.48e+08 Transitions= 9.47e+08 Memory= 18479.340 t= 2.31e+03 R=   2e+05
Depth=    2552 States= 3.49e+08 Transitions= 9.49e+08 Memory= 18513.672 t= 2.32e+03 R=   2e+05
Depth=    2552 States=  3.5e+08 Transitions= 9.52e+08 Memory= 18548.958 t= 2.32e+03 R=   2e+05
Depth=    2552 States= 3.51e+08 Transitions= 9.54e+08 Memory= 18583.767 t= 2.33e+03 R=   2e+05
Depth=    2552 States= 3.52e+08 Transitions= 9.56e+08 Memory= 18618.577 t= 2.33e+03 R=   2e+05
Depth=    2552 States= 3.53e+08 Transitions= 9.59e+08 Memory= 18653.386 t= 2.34e+03 R=   2e+05
Depth=    2552 States= 3.54e+08 Transitions= 9.61e+08 Memory= 18688.672 t= 2.35e+03 R=   2e+05
Depth=    2552 States= 3.55e+08 Transitions= 9.64e+08 Memory= 18725.865 t= 2.35e+03 R=   2e+05
Depth=    2552 States= 3.56e+08 Transitions= 9.66e+08 Memory= 18760.674 t= 2.36e+03 R=   2e+05
Depth=    2552 States= 3.57e+08 Transitions= 9.69e+08 Memory= 18794.053 t= 2.36e+03 R=   2e+05
Depth=    2552 States= 3.58e+08 Transitions= 9.71e+08 Memory= 18826.954 t= 2.37e+03 R=   2e+05
Depth=    2552 States= 3.59e+08 Transitions= 9.73e+08 Memory= 18859.379 t= 2.38e+03 R=   2e+05
Depth=    2552 States=  3.6e+08 Transitions= 9.76e+08 Memory= 18894.188 t= 2.38e+03 R=   2e+05
Depth=    2552 States= 3.61e+08 Transitions= 9.78e+08 Memory= 18929.951 t= 2.39e+03 R=   2e+05
Depth=    2552 States= 3.62e+08 Transitions= 9.81e+08 Memory= 18966.191 t= 2.39e+03 R=   2e+05
Depth=    2552 States= 3.63e+08 Transitions= 9.83e+08 Memory= 19001.000 t=  2.4e+03 R=   2e+05
Depth=    2552 States= 3.64e+08 Transitions= 9.86e+08 Memory= 19035.332 t= 2.41e+03 R=   2e+05
Depth=    2552 States= 3.65e+08 Transitions= 9.88e+08 Memory= 19070.141 t= 2.41e+03 R=   2e+05
Depth=    2552 States= 3.66e+08 Transitions= 9.91e+08 Memory= 19104.950 t= 2.42e+03 R=   2e+05
Depth=    2552 States= 3.67e+08 Transitions= 9.93e+08 Memory= 19141.667 t= 2.42e+03 R=   2e+05
Depth=    2552 States= 3.68e+08 Transitions= 9.95e+08 Memory= 19176.953 t= 2.43e+03 R=   2e+05
Depth=    2552 States= 3.69e+08 Transitions= 9.98e+08 Memory= 19211.762 t= 2.44e+03 R=   2e+05
Depth=    2552 States=  3.7e+08 Transitions=    1e+09 Memory= 19246.571 t= 2.44e+03 R=   2e+05
Depth=    2552 States= 3.71e+08 Transitions=    1e+09 Memory= 19282.811 t= 2.45e+03 R=   2e+05
Depth=    2552 States= 3.72e+08 Transitions= 1.01e+09 Memory= 19317.620 t= 2.45e+03 R=   2e+05
Depth=    2552 States= 3.73e+08 Transitions= 1.01e+09 Memory= 19353.859 t= 2.46e+03 R=   2e+05
Depth=    2552 States= 3.74e+08 Transitions= 1.01e+09 Memory= 19388.192 t= 2.47e+03 R=   2e+05
Depth=    2552 States= 3.75e+08 Transitions= 1.01e+09 Memory= 19423.001 t= 2.47e+03 R=   2e+05
Depth=    2552 States= 3.76e+08 Transitions= 1.02e+09 Memory= 19458.287 t= 2.48e+03 R=   2e+05
Depth=    2552 States= 3.77e+08 Transitions= 1.02e+09 Memory= 19494.526 t= 2.48e+03 R=   2e+05
Depth=    2552 States= 3.78e+08 Transitions= 1.02e+09 Memory= 19531.243 t= 2.49e+03 R=   2e+05
Depth=    2552 States= 3.79e+08 Transitions= 1.02e+09 Memory= 19567.482 t= 2.49e+03 R=   2e+05
Depth=    2552 States=  3.8e+08 Transitions= 1.02e+09 Memory= 19602.292 t=  2.5e+03 R=   2e+05
Depth=    2552 States= 3.81e+08 Transitions= 1.03e+09 Memory= 19637.101 t= 2.51e+03 R=   2e+05
Depth=    2552 States= 3.82e+08 Transitions= 1.03e+09 Memory= 19672.863 t= 2.51e+03 R=   2e+05
Depth=    2552 States= 3.83e+08 Transitions= 1.03e+09 Memory= 19710.057 t= 2.52e+03 R=   2e+05
Depth=    2552 States= 3.84e+08 Transitions= 1.03e+09 Memory= 19746.773 t= 2.52e+03 R=   2e+05
Depth=    2552 States= 3.85e+08 Transitions= 1.04e+09 Memory= 19783.967 t= 2.53e+03 R=   2e+05
Depth=    2552 States= 3.86e+08 Transitions= 1.04e+09 Memory= 19819.252 t= 2.54e+03 R=   2e+05
Depth=    2552 States= 3.87e+08 Transitions= 1.04e+09 Memory= 19856.446 t= 2.54e+03 R=   2e+05
Depth=    2552 States= 3.88e+08 Transitions= 1.04e+09 Memory= 19893.639 t= 2.55e+03 R=   2e+05
Depth=    2552 States= 3.89e+08 Transitions= 1.05e+09 Memory= 19929.402 t= 2.55e+03 R=   2e+05
Depth=    2552 States=  3.9e+08 Transitions= 1.05e+09 Memory= 19966.595 t= 2.56e+03 R=   2e+05
Depth=    2552 States= 3.91e+08 Transitions= 1.05e+09 Memory= 20001.404 t= 2.57e+03 R=   2e+05
Depth=    2552 States= 3.92e+08 Transitions= 1.05e+09 Memory= 20035.737 t= 2.57e+03 R=   2e+05
Depth=    2552 States= 3.93e+08 Transitions= 1.06e+09 Memory= 20070.546 t= 2.58e+03 R=   2e+05
Depth=    2552 States= 3.94e+08 Transitions= 1.06e+09 Memory= 20107.262 t= 2.58e+03 R=   2e+05
Depth=    2552 States= 3.95e+08 Transitions= 1.06e+09 Memory= 20143.979 t= 2.59e+03 R=   2e+05
Depth=    2552 States= 3.96e+08 Transitions= 1.06e+09 Memory= 20181.649 t=  2.6e+03 R=   2e+05
Depth=    2552 States= 3.97e+08 Transitions= 1.07e+09 Memory= 20215.981 t=  2.6e+03 R=   2e+05
Depth=    2552 States= 3.98e+08 Transitions= 1.07e+09 Memory= 20250.790 t= 2.61e+03 R=   2e+05
Depth=    2552 States= 3.99e+08 Transitions= 1.07e+09 Memory= 20288.460 t= 2.61e+03 R=   2e+05
Depth=    2552 States=    4e+08 Transitions= 1.07e+09 Memory= 20325.654 t= 2.62e+03 R=   2e+05
Depth=    2552 States= 4.01e+08 Transitions= 1.08e+09 Memory= 20361.893 t= 2.63e+03 R=   2e+05
Depth=    2552 States= 4.02e+08 Transitions= 1.08e+09 Memory= 20396.225 t= 2.63e+03 R=   2e+05
Depth=    2552 States= 4.03e+08 Transitions= 1.08e+09 Memory= 20431.035 t= 2.64e+03 R=   2e+05
Depth=    2552 States= 4.04e+08 Transitions= 1.08e+09 Memory= 20467.751 t= 2.64e+03 R=   2e+05
Depth=    2552 States= 4.05e+08 Transitions= 1.08e+09 Memory= 20503.991 t= 2.65e+03 R=   2e+05
Depth=    2552 States= 4.06e+08 Transitions= 1.09e+09 Memory= 20541.661 t= 2.65e+03 R=   2e+05
Depth=    2552 States= 4.07e+08 Transitions= 1.09e+09 Memory= 20579.331 t= 2.66e+03 R=   2e+05
Depth=    2552 States= 4.08e+08 Transitions= 1.09e+09 Memory= 20615.094 t= 2.67e+03 R=   2e+05
Depth=    2552 States= 4.09e+08 Transitions= 1.09e+09 Memory= 20652.764 t= 2.67e+03 R=   2e+05
Depth=    2552 States=  4.1e+08 Transitions=  1.1e+09 Memory= 20689.003 t= 2.68e+03 R=   2e+05
Depth=    2552 States= 4.11e+08 Transitions=  1.1e+09 Memory= 20726.674 t= 2.68e+03 R=   2e+05
Depth=    2552 States= 4.12e+08 Transitions=  1.1e+09 Memory= 20762.436 t= 2.69e+03 R=   2e+05
Depth=    2552 States= 4.13e+08 Transitions=  1.1e+09 Memory= 20800.583 t=  2.7e+03 R=   2e+05
Depth=    2552 States= 4.14e+08 Transitions= 1.11e+09 Memory= 20838.253 t=  2.7e+03 R=   2e+05
Depth=    2552 States= 4.15e+08 Transitions= 1.11e+09 Memory= 20874.016 t= 2.71e+03 R=   2e+05
Depth=    2552 States= 4.16e+08 Transitions= 1.11e+09 Memory= 20910.256 t= 2.71e+03 R=   2e+05
Depth=    2552 States= 4.17e+08 Transitions= 1.11e+09 Memory= 20945.542 t= 2.72e+03 R=   2e+05
Depth=    2552 States= 4.18e+08 Transitions= 1.12e+09 Memory= 20979.874 t= 2.73e+03 R=   2e+05
Depth=    2552 States= 4.19e+08 Transitions= 1.12e+09 Memory= 21016.114 t= 2.73e+03 R=   2e+05
Depth=    2552 States=  4.2e+08 Transitions= 1.12e+09 Memory= 21052.830 t= 2.74e+03 R=   2e+05
Depth=    2552 States= 4.21e+08 Transitions= 1.12e+09 Memory= 21087.639 t= 2.74e+03 R=   2e+05
Depth=    2552 States= 4.22e+08 Transitions= 1.13e+09 Memory= 21121.972 t= 2.75e+03 R=   2e+05
Depth=    2552 States= 4.23e+08 Transitions= 1.13e+09 Memory= 21156.304 t= 2.75e+03 R=   2e+05
Depth=    2552 States= 4.24e+08 Transitions= 1.13e+09 Memory= 21190.636 t= 2.76e+03 R=   2e+05
Depth=    2552 States= 4.25e+08 Transitions= 1.13e+09 Memory= 21224.968 t= 2.77e+03 R=   2e+05
Depth=    2552 States= 4.26e+08 Transitions= 1.14e+09 Memory= 21259.301 t= 2.77e+03 R=   2e+05
Depth=    2552 States= 4.27e+08 Transitions= 1.14e+09 Memory= 21293.633 t= 2.78e+03 R=   2e+05
Depth=    2552 States= 4.28e+08 Transitions= 1.14e+09 Memory= 21328.442 t= 2.78e+03 R=   2e+05
Depth=    2552 States= 4.29e+08 Transitions= 1.14e+09 Memory= 21365.159 t= 2.79e+03 R=   2e+05
Depth=    2552 States=  4.3e+08 Transitions= 1.15e+09 Memory= 21400.921 t=  2.8e+03 R=   2e+05
Depth=    2552 States= 4.31e+08 Transitions= 1.15e+09 Memory= 21437.161 t=  2.8e+03 R=   2e+05
Depth=    2552 States= 4.32e+08 Transitions= 1.15e+09 Memory= 21471.493 t= 2.81e+03 R=   2e+05
Depth=    2552 States= 4.33e+08 Transitions= 1.15e+09 Memory= 21505.826 t= 2.81e+03 R=   2e+05
Depth=    2552 States= 4.34e+08 Transitions= 1.15e+09 Memory= 21540.158 t= 2.82e+03 R=   2e+05
Depth=    2552 States= 4.35e+08 Transitions= 1.16e+09 Memory= 21574.490 t= 2.83e+03 R=   2e+05
Depth=    2552 States= 4.36e+08 Transitions= 1.16e+09 Memory= 21608.822 t= 2.83e+03 R=   2e+05
Depth=    2552 States= 4.37e+08 Transitions= 1.16e+09 Memory= 21643.155 t= 2.84e+03 R=   2e+05
Depth=    2552 States= 4.38e+08 Transitions= 1.16e+09 Memory= 21679.871 t= 2.84e+03 R=   2e+05
Depth=    2552 States= 4.39e+08 Transitions= 1.17e+09 Memory= 21716.111 t= 2.85e+03 R=   2e+05
Depth=    2552 States=  4.4e+08 Transitions= 1.17e+09 Memory= 21754.734 t= 2.85e+03 R=   2e+05
Depth=    2552 States= 4.41e+08 Transitions= 1.17e+09 Memory= 21791.451 t= 2.86e+03 R=   2e+05
Depth=    2552 States= 4.42e+08 Transitions= 1.17e+09 Memory= 21828.167 t= 2.87e+03 R=   2e+05
Depth=    2552 States= 4.43e+08 Transitions= 1.18e+09 Memory= 21864.407 t= 2.87e+03 R=   2e+05
Depth=    2552 States= 4.44e+08 Transitions= 1.18e+09 Memory= 21900.647 t= 2.88e+03 R=   2e+05
Depth=    2552 States= 4.45e+08 Transitions= 1.18e+09 Memory= 21935.933 t= 2.88e+03 R=   2e+05
Depth=    2552 States= 4.46e+08 Transitions= 1.18e+09 Memory= 21970.265 t= 2.89e+03 R=   2e+05
Depth=    2552 States= 4.47e+08 Transitions= 1.19e+09 Memory= 22004.597 t=  2.9e+03 R=   2e+05
Depth=    2552 States= 4.48e+08 Transitions= 1.19e+09 Memory= 22039.883 t=  2.9e+03 R=   2e+05
Depth=    2552 States= 4.49e+08 Transitions= 1.19e+09 Memory= 22076.123 t= 2.91e+03 R=   2e+05
Depth=    2552 States=  4.5e+08 Transitions= 1.19e+09 Memory= 22112.362 t= 2.91e+03 R=   2e+05
Depth=    2552 States= 4.51e+08 Transitions=  1.2e+09 Memory= 22146.695 t= 2.92e+03 R=   2e+05
Depth=    2552 States= 4.52e+08 Transitions=  1.2e+09 Memory= 22181.027 t= 2.93e+03 R=   2e+05
Depth=    2552 States= 4.53e+08 Transitions=  1.2e+09 Memory= 22217.267 t= 2.93e+03 R=   2e+05
Depth=    2552 States= 4.54e+08 Transitions=  1.2e+09 Memory= 22253.506 t= 2.94e+03 R=   2e+05
Depth=    2552 States= 4.55e+08 Transitions= 1.21e+09 Memory= 22287.838 t= 2.94e+03 R=   2e+05
Depth=    2552 States= 4.56e+08 Transitions= 1.21e+09 Memory= 22322.648 t= 2.95e+03 R=   2e+05
Depth=    2552 States= 4.57e+08 Transitions= 1.21e+09 Memory= 22360.318 t= 2.96e+03 R=   2e+05
Depth=    2552 States= 4.58e+08 Transitions= 1.21e+09 Memory= 22396.557 t= 2.96e+03 R=   2e+05
Depth=    2552 States= 4.59e+08 Transitions= 1.22e+09 Memory= 22432.797 t= 2.97e+03 R=   2e+05
Depth=    2552 States=  4.6e+08 Transitions= 1.22e+09 Memory= 22469.037 t= 2.97e+03 R=   2e+05
Depth=    2552 States= 4.61e+08 Transitions= 1.22e+09 Memory= 22503.369 t= 2.98e+03 R=   2e+05
Depth=    2552 States= 4.62e+08 Transitions= 1.22e+09 Memory= 22539.132 t= 2.98e+03 R=   2e+05
Depth=    2552 States= 4.63e+08 Transitions= 1.22e+09 Memory= 22574.418 t= 2.99e+03 R=   2e+05
Depth=    2552 States= 4.64e+08 Transitions= 1.23e+09 Memory= 22612.088 t=    3e+03 R=   2e+05
Depth=    2552 States= 4.65e+08 Transitions= 1.23e+09 Memory= 22648.327 t=    3e+03 R=   2e+05
Depth=    2552 States= 4.66e+08 Transitions= 1.23e+09 Memory= 22685.521 t= 3.01e+03 R=   2e+05
Depth=    2552 States= 4.67e+08 Transitions= 1.23e+09 Memory= 22722.237 t= 3.01e+03 R=   2e+05
Depth=    2552 States= 4.68e+08 Transitions= 1.24e+09 Memory= 22758.477 t= 3.02e+03 R=   2e+05
Depth=    2552 States= 4.69e+08 Transitions= 1.24e+09 Memory= 22795.670 t= 3.03e+03 R=   2e+05
Depth=    2552 States=  4.7e+08 Transitions= 1.24e+09 Memory= 22831.433 t= 3.03e+03 R=   2e+05
Depth=    2552 States= 4.71e+08 Transitions= 1.24e+09 Memory= 22867.672 t= 3.04e+03 R=   2e+05
Depth=    2552 States= 4.72e+08 Transitions= 1.25e+09 Memory= 22905.819 t= 3.04e+03 R=   2e+05
Depth=    2552 States= 4.73e+08 Transitions= 1.25e+09 Memory= 22940.629 t= 3.05e+03 R=   2e+05
Depth=    2552 States= 4.74e+08 Transitions= 1.25e+09 Memory= 22974.961 t= 3.06e+03 R=   2e+05
Depth=    2552 States= 4.75e+08 Transitions= 1.25e+09 Memory= 23009.293 t= 3.06e+03 R=   2e+05
Depth=    2552 States= 4.76e+08 Transitions= 1.26e+09 Memory= 23043.148 t= 3.07e+03 R=   2e+05
Depth=    2552 States= 4.77e+08 Transitions= 1.26e+09 Memory= 23077.004 t= 3.07e+03 R=   2e+05
Depth=    2552 States= 4.78e+08 Transitions= 1.26e+09 Memory= 23111.813 t= 3.08e+03 R=   2e+05
Depth=    2552 States= 4.79e+08 Transitions= 1.26e+09 Memory= 23165.696 t= 3.09e+03 R=   2e+05
Depth=    2552 States=  4.8e+08 Transitions= 1.27e+09 Memory= 23231.976 t= 3.09e+03 R=   2e+05
Depth=    2552 States= 4.81e+08 Transitions= 1.27e+09 Memory= 23298.733 t=  3.1e+03 R=   2e+05
Depth=    2552 States= 4.82e+08 Transitions= 1.27e+09 Memory= 23363.106 t= 3.11e+03 R=   2e+05
Depth=    2552 States= 4.83e+08 Transitions= 1.28e+09 Memory= 23428.433 t= 3.12e+03 R=   2e+05
Depth=    2552 States= 4.84e+08 Transitions= 1.28e+09 Memory= 23493.760 t= 3.12e+03 R=   2e+05
Depth=    2552 States= 4.85e+08 Transitions= 1.28e+09 Memory= 23558.609 t= 3.13e+03 R=   2e+05
Depth=    2552 States= 4.86e+08 Transitions= 1.28e+09 Memory= 23621.075 t= 3.14e+03 R=   2e+05
Depth=    2552 States= 4.87e+08 Transitions= 1.29e+09 Memory= 23684.971 t= 3.15e+03 R=   2e+05
Depth=    2552 States= 4.88e+08 Transitions= 1.29e+09 Memory= 23753.159 t= 3.15e+03 R=   2e+05
Depth=    2552 States= 4.89e+08 Transitions= 1.29e+09 Memory= 23823.254 t= 3.16e+03 R=   2e+05
Depth=    2552 States=  4.9e+08 Transitions=  1.3e+09 Memory= 23892.395 t= 3.17e+03 R=   2e+05
Depth=    2552 States= 4.91e+08 Transitions=  1.3e+09 Memory= 23961.060 t= 3.18e+03 R=   2e+05
Depth=    2552 States= 4.92e+08 Transitions=  1.3e+09 Memory= 24029.725 t= 3.18e+03 R=   2e+05
Depth=    2552 States= 4.93e+08 Transitions=  1.3e+09 Memory= 24097.912 t= 3.19e+03 R=   2e+05
Depth=    2552 States= 4.94e+08 Transitions= 1.31e+09 Memory= 24166.577 t=  3.2e+03 R=   2e+05
Depth=    2552 States= 4.95e+08 Transitions= 1.31e+09 Memory= 24236.195 t= 3.21e+03 R=   2e+05
Depth=    2552 States= 4.96e+08 Transitions= 1.31e+09 Memory= 24304.383 t= 3.21e+03 R=   2e+05
Depth=    2552 States= 4.97e+08 Transitions= 1.32e+09 Memory= 24373.047 t= 3.22e+03 R=   2e+05
Depth=    2552 States= 4.98e+08 Transitions= 1.32e+09 Memory= 24443.142 t= 3.23e+03 R=   2e+05
Depth=    2552 States= 4.99e+08 Transitions= 1.32e+09 Memory= 24513.237 t= 3.24e+03 R=   2e+05
Depth=    2552 States=    5e+08 Transitions= 1.32e+09 Memory= 24581.902 t= 3.24e+03 R=   2e+05
Depth=    2552 States= 5.01e+08 Transitions= 1.33e+09 Memory= 24650.567 t= 3.25e+03 R=   2e+05
Depth=    2552 States= 5.02e+08 Transitions= 1.33e+09 Memory= 24719.231 t= 3.26e+03 R=   2e+05
Depth=    2552 States= 5.03e+08 Transitions= 1.33e+09 Memory= 24788.372 t= 3.27e+03 R=   2e+05
Depth=    2552 States= 5.04e+08 Transitions= 1.34e+09 Memory= 24857.037 t= 3.27e+03 R=   2e+05
Depth=    2552 States= 5.05e+08 Transitions= 1.34e+09 Memory= 24926.655 t= 3.28e+03 R=   2e+05
Depth=    2552 States= 5.06e+08 Transitions= 1.34e+09 Memory= 24996.273 t= 3.29e+03 R=   2e+05
Depth=    2552 States= 5.07e+08 Transitions= 1.34e+09 Memory= 25066.369 t=  3.3e+03 R=   2e+05
Depth=    2552 States= 5.08e+08 Transitions= 1.35e+09 Memory= 25135.033 t=  3.3e+03 R=   2e+05
Depth=    2552 States= 5.09e+08 Transitions= 1.35e+09 Memory= 25203.221 t= 3.31e+03 R=   2e+05
Depth=    2552 States=  5.1e+08 Transitions= 1.35e+09 Memory= 25271.885 t= 3.32e+03 R=   2e+05
Depth=    2552 States= 5.11e+08 Transitions= 1.35e+09 Memory= 25341.980 t= 3.33e+03 R=   2e+05
Depth=    2552 States= 5.12e+08 Transitions= 1.36e+09 Memory= 25410.645 t= 3.33e+03 R=   2e+05
Depth=    2552 States= 5.13e+08 Transitions= 1.36e+09 Memory= 25479.310 t= 3.34e+03 R=   2e+05
Depth=    2552 States= 5.14e+08 Transitions= 1.36e+09 Memory= 25547.974 t= 3.35e+03 R=   2e+05
Depth=    2552 States= 5.15e+08 Transitions= 1.37e+09 Memory= 25617.115 t= 3.36e+03 R=   2e+05
Depth=    2552 States= 5.16e+08 Transitions= 1.37e+09 Memory= 25682.442 t= 3.37e+03 R=   2e+05
Depth=    2552 States= 5.17e+08 Transitions= 1.37e+09 Memory= 25748.723 t= 3.38e+03 R=   2e+05
Depth=    2552 States= 5.18e+08 Transitions= 1.38e+09 Memory= 25817.387 t= 3.39e+03 R=   2e+05
Depth=    2552 States= 5.19e+08 Transitions= 1.38e+09 Memory= 25886.052 t=  3.4e+03 R=   2e+05
Depth=    2552 States=  5.2e+08 Transitions= 1.39e+09 Memory= 25954.716 t= 3.41e+03 R=   2e+05
Depth=    2552 States= 5.21e+08 Transitions= 1.39e+09 Memory= 26022.904 t= 3.42e+03 R=   2e+05
Depth=    2552 States= 5.22e+08 Transitions= 1.39e+09 Memory= 26091.568 t= 3.43e+03 R=   2e+05
Depth=    2552 States= 5.23e+08 Transitions=  1.4e+09 Memory= 26160.233 t= 3.44e+03 R=   2e+05
Depth=    2552 States= 5.24e+08 Transitions=  1.4e+09 Memory= 26229.374 t= 3.45e+03 R=   2e+05
Depth=    2552 States= 5.25e+08 Transitions=  1.4e+09 Memory= 26300.423 t= 3.46e+03 R=   2e+05
Depth=    2552 States= 5.26e+08 Transitions= 1.41e+09 Memory= 26370.518 t= 3.46e+03 R=   2e+05
Depth=    2552 States= 5.27e+08 Transitions= 1.41e+09 Memory= 26437.275 t= 3.47e+03 R=   2e+05
Depth=    2552 States= 5.28e+08 Transitions= 1.41e+09 Memory= 26508.324 t= 3.48e+03 R=   2e+05
Depth=    2552 States= 5.29e+08 Transitions= 1.42e+09 Memory= 26578.419 t= 3.49e+03 R=   2e+05
Depth=    2552 States=  5.3e+08 Transitions= 1.42e+09 Memory= 26646.607 t=  3.5e+03 R=   2e+05
Depth=    2552 States= 5.31e+08 Transitions= 1.42e+09 Memory= 26715.748 t= 3.51e+03 R=   2e+05
Depth=    2552 States= 5.32e+08 Transitions= 1.43e+09 Memory= 26785.843 t= 3.51e+03 R=   2e+05
Depth=    2552 States= 5.33e+08 Transitions= 1.43e+09 Memory= 26854.985 t= 3.52e+03 R=   2e+05
Depth=    2552 States= 5.34e+08 Transitions= 1.43e+09 Memory= 26924.126 t= 3.53e+03 R=   2e+05
Depth=    2552 States= 5.35e+08 Transitions= 1.43e+09 Memory= 26993.744 t= 3.54e+03 R=   2e+05
Depth=    2552 States= 5.36e+08 Transitions= 1.44e+09 Memory= 27064.793 t= 3.55e+03 R=   2e+05
Depth=    2552 States= 5.37e+08 Transitions= 1.44e+09 Memory= 27134.888 t= 3.55e+03 R=   2e+05
pan: resizing hashtable to -w30..  done
Depth=    2552 States= 5.38e+08 Transitions= 1.44e+09 Memory= 35326.888 t= 3.64e+03 R=   1e+05
Depth=    2552 States= 5.39e+08 Transitions= 1.45e+09 Memory= 35326.888 t= 3.65e+03 R=   1e+05
Depth=    2552 States=  5.4e+08 Transitions= 1.45e+09 Memory= 35326.888 t= 3.66e+03 R=   1e+05
Depth=    2552 States= 5.41e+08 Transitions= 1.45e+09 Memory= 35350.730 t= 3.67e+03 R=   1e+05
Depth=    2552 States= 5.42e+08 Transitions= 1.46e+09 Memory= 35419.871 t= 3.67e+03 R=   1e+05
Depth=    2552 States= 5.43e+08 Transitions= 1.46e+09 Memory= 35489.966 t= 3.68e+03 R=   1e+05
Depth=    2552 States= 5.44e+08 Transitions= 1.46e+09 Memory= 35561.015 t= 3.69e+03 R=   1e+05
Depth=    2552 States= 5.45e+08 Transitions= 1.46e+09 Memory= 35632.064 t=  3.7e+03 R=   1e+05
Depth=    2552 States= 5.46e+08 Transitions= 1.47e+09 Memory= 35702.636 t=  3.7e+03 R=   1e+05
Depth=    2552 States= 5.47e+08 Transitions= 1.47e+09 Memory= 35773.685 t= 3.71e+03 R=   1e+05
Depth=    2552 States= 5.48e+08 Transitions= 1.47e+09 Memory= 35842.826 t= 3.72e+03 R=   1e+05
Depth=    2552 States= 5.49e+08 Transitions= 1.48e+09 Memory= 35911.967 t= 3.73e+03 R=   1e+05
Depth=    2552 States=  5.5e+08 Transitions= 1.48e+09 Memory= 35983.016 t= 3.74e+03 R=   1e+05
Depth=    2552 States= 5.51e+08 Transitions= 1.48e+09 Memory= 36052.634 t= 3.74e+03 R=   1e+05
Depth=    2552 States= 5.52e+08 Transitions= 1.49e+09 Memory= 36121.299 t= 3.75e+03 R=   1e+05
Depth=    2552 States= 5.53e+08 Transitions= 1.49e+09 Memory= 36189.963 t= 3.76e+03 R=   1e+05
Depth=    2552 States= 5.54e+08 Transitions= 1.49e+09 Memory= 36258.628 t= 3.77e+03 R=   1e+05
Depth=    2552 States= 5.55e+08 Transitions= 1.49e+09 Memory= 36326.816 t= 3.77e+03 R=   1e+05
Depth=    2552 States= 5.56e+08 Transitions=  1.5e+09 Memory= 36395.480 t= 3.78e+03 R=   1e+05
Depth=    2552 States= 5.57e+08 Transitions=  1.5e+09 Memory= 36464.145 t= 3.79e+03 R=   1e+05
Depth=    2552 States= 5.58e+08 Transitions=  1.5e+09 Memory= 36523.273 t=  3.8e+03 R=   1e+05
Depth=    2552 States= 5.59e+08 Transitions= 1.51e+09 Memory= 36592.891 t=  3.8e+03 R=   1e+05
Depth=    2552 States=  5.6e+08 Transitions= 1.51e+09 Memory= 36661.555 t= 3.81e+03 R=   1e+05
Depth=    2552 States= 5.61e+08 Transitions= 1.51e+09 Memory= 36730.220 t= 3.82e+03 R=   1e+05
Depth=    2552 States= 5.62e+08 Transitions= 1.51e+09 Memory= 36798.884 t= 3.82e+03 R=   1e+05
Depth=    2552 States= 5.63e+08 Transitions= 1.52e+09 Memory= 36867.072 t= 3.83e+03 R=   1e+05
Depth=    2552 States= 5.64e+08 Transitions= 1.52e+09 Memory= 36935.737 t= 3.84e+03 R=   1e+05
Depth=    2552 States= 5.65e+08 Transitions= 1.52e+09 Memory= 37004.401 t= 3.85e+03 R=   1e+05
Depth=    2552 States= 5.66e+08 Transitions= 1.53e+09 Memory= 37073.543 t= 3.86e+03 R=   1e+05
Depth=    2552 States= 5.67e+08 Transitions= 1.53e+09 Memory= 37143.161 t= 3.86e+03 R=   1e+05
Depth=    2552 States= 5.68e+08 Transitions= 1.53e+09 Memory= 37211.825 t= 3.87e+03 R=   1e+05
Depth=    2552 States= 5.69e+08 Transitions= 1.54e+09 Memory= 37280.490 t= 3.88e+03 R=   1e+05
Depth=    2552 States=  5.7e+08 Transitions= 1.54e+09 Memory= 37349.155 t= 3.89e+03 R=   1e+05
Depth=    2552 States= 5.71e+08 Transitions= 1.54e+09 Memory= 37419.250 t= 3.89e+03 R=   1e+05
Depth=    2552 States= 5.72e+08 Transitions= 1.55e+09 Memory= 37488.391 t=  3.9e+03 R=   1e+05
Depth=    2552 States= 5.73e+08 Transitions= 1.55e+09 Memory= 37557.056 t= 3.91e+03 R=   1e+05
Depth=    2552 States= 5.74e+08 Transitions= 1.55e+09 Memory= 37626.197 t= 3.92e+03 R=   1e+05
Depth=    2552 States= 5.75e+08 Transitions= 1.55e+09 Memory= 37695.338 t= 3.92e+03 R=   1e+05
Depth=    2552 States= 5.76e+08 Transitions= 1.56e+09 Memory= 37764.003 t= 3.93e+03 R=   1e+05
Depth=    2552 States= 5.77e+08 Transitions= 1.56e+09 Memory= 37835.052 t= 3.94e+03 R=   1e+05
Depth=    2552 States= 5.78e+08 Transitions= 1.56e+09 Memory= 37905.147 t= 3.95e+03 R=   1e+05
Depth=    2552 States= 5.79e+08 Transitions= 1.57e+09 Memory= 37974.765 t= 3.95e+03 R=   1e+05
Depth=    2552 States=  5.8e+08 Transitions= 1.57e+09 Memory= 38042.953 t= 3.96e+03 R=   1e+05
Depth=    2552 States= 5.81e+08 Transitions= 1.57e+09 Memory= 38114.001 t= 3.97e+03 R=   1e+05
Depth=    2552 States= 5.82e+08 Transitions= 1.57e+09 Memory= 38183.620 t= 3.97e+03 R=   1e+05
Depth=    2552 States= 5.83e+08 Transitions= 1.58e+09 Memory= 38252.284 t= 3.98e+03 R=   1e+05
Depth=    2552 States= 5.84e+08 Transitions= 1.58e+09 Memory= 38322.379 t= 3.99e+03 R=   1e+05
Depth=    2552 States= 5.85e+08 Transitions= 1.58e+09 Memory= 38393.428 t=    4e+03 R=   1e+05
Depth=    2552 States= 5.86e+08 Transitions= 1.59e+09 Memory= 38462.569 t= 4.01e+03 R=   1e+05
Depth=    2552 States= 5.87e+08 Transitions= 1.59e+09 Memory= 38531.234 t= 4.01e+03 R=   1e+05
Depth=    2552 States= 5.88e+08 Transitions= 1.59e+09 Memory= 38598.945 t= 4.02e+03 R=   1e+05
Depth=    2552 States= 5.89e+08 Transitions=  1.6e+09 Memory= 38666.179 t= 4.03e+03 R=   1e+05
Depth=    2552 States=  5.9e+08 Transitions=  1.6e+09 Memory= 38734.366 t= 4.04e+03 R=   1e+05
Depth=    2552 States= 5.91e+08 Transitions=  1.6e+09 Memory= 38799.693 t= 4.05e+03 R=   1e+05
Depth=    2552 States= 5.92e+08 Transitions= 1.61e+09 Memory= 38866.450 t= 4.06e+03 R=   1e+05
Depth=    2552 States= 5.93e+08 Transitions= 1.61e+09 Memory= 38935.115 t= 4.07e+03 R=   1e+05
Depth=    2552 States= 5.94e+08 Transitions= 1.62e+09 Memory= 39003.779 t= 4.08e+03 R=   1e+05
Depth=    2552 States= 5.95e+08 Transitions= 1.62e+09 Memory= 39072.444 t= 4.09e+03 R=   1e+05
Depth=    2552 States= 5.96e+08 Transitions= 1.62e+09 Memory= 39141.109 t=  4.1e+03 R=   1e+05
Depth=    2552 States= 5.97e+08 Transitions= 1.63e+09 Memory= 39209.296 t= 4.11e+03 R=   1e+05
Depth=    2552 States= 5.98e+08 Transitions= 1.63e+09 Memory= 39277.961 t= 4.11e+03 R=   1e+05
Depth=    2552 States= 5.99e+08 Transitions= 1.64e+09 Memory= 39345.672 t= 4.12e+03 R=   1e+05
Depth=    2552 States=    6e+08 Transitions= 1.64e+09 Memory= 39413.859 t= 4.13e+03 R=   1e+05
Depth=    2552 States= 6.01e+08 Transitions= 1.64e+09 Memory= 39482.524 t= 4.14e+03 R=   1e+05
Depth=    2552 States= 6.02e+08 Transitions= 1.65e+09 Memory= 39550.712 t= 4.15e+03 R=   1e+05
Depth=    2552 States= 6.03e+08 Transitions= 1.65e+09 Memory= 39619.376 t= 4.16e+03 R=   1e+05
Depth=    2552 States= 6.04e+08 Transitions= 1.66e+09 Memory= 39688.041 t= 4.17e+03 R=   1e+05
Depth=    2552 States= 6.05e+08 Transitions= 1.66e+09 Memory= 39756.705 t= 4.18e+03 R=   1e+05
Depth=    2552 States= 6.06e+08 Transitions= 1.66e+09 Memory= 39824.893 t= 4.19e+03 R=   1e+05
Depth=    2552 States= 6.07e+08 Transitions= 1.67e+09 Memory= 39893.558 t=  4.2e+03 R=   1e+05
Depth=    2552 States= 6.08e+08 Transitions= 1.67e+09 Memory= 39961.745 t= 4.21e+03 R=   1e+05
Depth=    2552 States= 6.09e+08 Transitions= 1.68e+09 Memory= 40030.410 t= 4.22e+03 R=   1e+05
Depth=    2552 States=  6.1e+08 Transitions= 1.68e+09 Memory= 40099.074 t= 4.23e+03 R=   1e+05
Depth=    2552 States= 6.11e+08 Transitions= 1.68e+09 Memory= 40167.739 t= 4.24e+03 R=   1e+05
Depth=    2552 States= 6.12e+08 Transitions= 1.69e+09 Memory= 40235.927 t= 4.25e+03 R=   1e+05
Depth=    2552 States= 6.13e+08 Transitions= 1.69e+09 Memory= 40304.591 t= 4.26e+03 R=   1e+05
Depth=    2552 States= 6.14e+08 Transitions= 1.69e+09 Memory= 40357.997 t= 4.27e+03 R=   1e+05
Depth=    2552 States= 6.15e+08 Transitions=  1.7e+09 Memory= 40407.588 t= 4.28e+03 R=   1e+05
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
Depth=    2538 States=    2e+06 Transitions= 3.92e+06 Memory=   262.869 t=     8.21 R=   2e+05
Depth=    2538 States=    3e+06 Transitions= 5.89e+06 Memory=   325.811 t=     12.4 R=   2e+05
Depth=    2538 States=    4e+06 Transitions= 7.87e+06 Memory=   386.846 t=     16.6 R=   2e+05
Depth=    2538 States=    5e+06 Transitions= 9.83e+06 Memory=   448.358 t=     20.7 R=   2e+05
Depth=    2538 States=    6e+06 Transitions= 1.18e+07 Memory=   509.394 t=       25 R=   2e+05
Depth=    2538 States=    7e+06 Transitions= 1.38e+07 Memory=   572.336 t=     29.2 R=   2e+05
Depth=    2538 States=    8e+06 Transitions= 1.57e+07 Memory=   633.371 t=     33.4 R=   2e+05
Depth=    2538 States=    9e+06 Transitions= 1.77e+07 Memory=   694.883 t=     37.6 R=   2e+05
Depth=    2538 States=    1e+07 Transitions= 1.97e+07 Memory=   761.640 t=     41.9 R=   2e+05
Depth=    2538 States=  1.1e+07 Transitions= 2.16e+07 Memory=   833.166 t=     46.1 R=   2e+05
Depth=    2538 States=  1.2e+07 Transitions= 2.36e+07 Memory=   901.831 t=     50.4 R=   2e+05
Depth=    2538 States=  1.3e+07 Transitions= 2.56e+07 Memory=   970.972 t=     54.7 R=   2e+05
Depth=    2538 States=  1.4e+07 Transitions= 2.75e+07 Memory=  1039.637 t=       59 R=   2e+05
Depth=    2538 States=  1.5e+07 Transitions= 2.95e+07 Memory=  1109.255 t=     63.3 R=   2e+05
Depth=    2538 States=  1.6e+07 Transitions= 3.15e+07 Memory=  1177.919 t=     67.7 R=   2e+05
Depth=    2538 States=  1.7e+07 Transitions= 3.34e+07 Memory=  1246.107 t=     72.1 R=   2e+05
Depth=    2538 States=  1.8e+07 Transitions= 3.54e+07 Memory=  1312.864 t=     76.5 R=   2e+05
Depth=    2538 States=  1.9e+07 Transitions= 3.74e+07 Memory=  1379.145 t=     80.9 R=   2e+05
Depth=    2538 States=    2e+07 Transitions= 3.94e+07 Memory=  1448.763 t=     85.5 R=   2e+05
Depth=    2538 States=  2.1e+07 Transitions= 4.13e+07 Memory=  1518.381 t=       90 R=   2e+05
Depth=    2538 States=  2.2e+07 Transitions= 4.33e+07 Memory=  1584.661 t=     94.5 R=   2e+05
Depth=    2538 States=  2.3e+07 Transitions= 4.53e+07 Memory=  1650.942 t=     99.1 R=   2e+05
Depth=    2538 States=  2.4e+07 Transitions= 4.73e+07 Memory=  1717.222 t=      104 R=   2e+05
Depth=    2538 States=  2.5e+07 Transitions= 4.92e+07 Memory=  1784.456 t=      108 R=   2e+05
Depth=    2538 States=  2.6e+07 Transitions= 5.12e+07 Memory=  1853.121 t=      113 R=   2e+05
Depth=    2538 States=  2.7e+07 Transitions= 5.32e+07 Memory=  1923.693 t=      117 R=   2e+05
Depth=    2552 States=  2.8e+07 Transitions= 5.51e+07 Memory=  1993.788 t=      122 R=   2e+05
Depth=    2552 States=  2.9e+07 Transitions= 5.71e+07 Memory=  2065.313 t=      127 R=   2e+05
Depth=    2552 States=    3e+07 Transitions= 5.91e+07 Memory=  2133.501 t=      132 R=   2e+05
Depth=    2552 States=  3.1e+07 Transitions=  6.1e+07 Memory=  2201.689 t=      136 R=   2e+05
Depth=    2552 States=  3.2e+07 Transitions=  6.3e+07 Memory=  2270.830 t=      141 R=   2e+05
Depth=    2552 States=  3.3e+07 Transitions=  6.5e+07 Memory=  2340.925 t=      146 R=   2e+05
Depth=    2552 States=  3.4e+07 Transitions= 6.69e+07 Memory=  2409.590 t=      151 R=   2e+05
pan: resizing hashtable to -w26..  done
Depth=    2552 States=  3.5e+07 Transitions= 6.89e+07 Memory=  2974.042 t=      160 R=   2e+05
Depth=    2552 States=  3.6e+07 Transitions= 7.09e+07 Memory=  3044.137 t=      164 R=   2e+05
Depth=    2552 States=  3.7e+07 Transitions= 7.29e+07 Memory=  3111.848 t=      169 R=   2e+05
Depth=    2552 States=  3.8e+07 Transitions= 7.48e+07 Memory=  3177.174 t=      173 R=   2e+05
Depth=    2552 States=  3.9e+07 Transitions= 7.68e+07 Memory=  3244.885 t=      177 R=   2e+05
Depth=    2552 States=    4e+07 Transitions= 7.88e+07 Memory=  3313.550 t=      182 R=   2e+05
Depth=    2552 States=  4.1e+07 Transitions= 8.08e+07 Memory=  3381.261 t=      186 R=   2e+05
Depth=    2552 States=  4.2e+07 Transitions= 8.27e+07 Memory=  3450.879 t=      190 R=   2e+05
Depth=    2552 States=  4.3e+07 Transitions= 8.47e+07 Memory=  3519.067 t=      195 R=   2e+05
Depth=    2552 States=  4.4e+07 Transitions= 8.67e+07 Memory=  3590.592 t=      199 R=   2e+05
Depth=    2552 States=  4.5e+07 Transitions= 8.87e+07 Memory=  3659.257 t=      204 R=   2e+05
Depth=    2552 States=  4.6e+07 Transitions= 9.06e+07 Memory=  3730.782 t=      208 R=   2e+05
Depth=    2552 States=  4.7e+07 Transitions= 9.26e+07 Memory=  3801.831 t=      212 R=   2e+05
Depth=    2552 States=  4.8e+07 Transitions= 9.46e+07 Memory=  3871.449 t=      217 R=   2e+05
Depth=    2552 States=  4.9e+07 Transitions= 9.65e+07 Memory=  3935.345 t=      221 R=   2e+05
Depth=    2552 States=    5e+07 Transitions= 9.85e+07 Memory=  4005.441 t=      226 R=   2e+05
Depth=    2552 States=  5.1e+07 Transitions=    1e+08 Memory=  4075.536 t=      230 R=   2e+05
Depth=    2552 States=  5.2e+07 Transitions= 1.02e+08 Memory=  4145.154 t=      235 R=   2e+05
Depth=    2552 States=  5.3e+07 Transitions= 1.04e+08 Memory=  4212.865 t=      239 R=   2e+05
Depth=    2552 States=  5.4e+07 Transitions= 1.06e+08 Memory=  4279.145 t=      244 R=   2e+05
Depth=    2552 States=  5.5e+07 Transitions= 1.08e+08 Memory=  4343.041 t=      248 R=   2e+05
Depth=    2552 States=  5.6e+07 Transitions=  1.1e+08 Memory=  4408.368 t=      253 R=   2e+05
Depth=    2552 States=  5.7e+07 Transitions= 1.12e+08 Memory=  4477.033 t=      257 R=   2e+05
Depth=    2552 States=  5.8e+07 Transitions= 1.14e+08 Memory=  4548.081 t=      262 R=   2e+05
Depth=    2552 States=  5.9e+07 Transitions= 1.16e+08 Memory=  4615.315 t=      267 R=   2e+05
Depth=    2552 States=    6e+07 Transitions= 1.18e+08 Memory=  4684.457 t=      271 R=   2e+05
Depth=    2552 States=  6.1e+07 Transitions=  1.2e+08 Memory=  4753.121 t=      276 R=   2e+05
Depth=    2552 States=  6.2e+07 Transitions= 1.22e+08 Memory=  4820.355 t=      280 R=   2e+05
Depth=    2552 States=  6.3e+07 Transitions= 1.24e+08 Memory=  4885.682 t=      285 R=   2e+05
Depth=    2552 States=  6.4e+07 Transitions= 1.26e+08 Memory=  4954.823 t=      289 R=   2e+05
Depth=    2552 States=  6.5e+07 Transitions= 1.28e+08 Memory=  5022.057 t=      293 R=   2e+05
Depth=    2552 States=  6.6e+07 Transitions=  1.3e+08 Memory=  5086.907 t=      298 R=   2e+05
Depth=    2552 States=  6.7e+07 Transitions= 1.32e+08 Memory=  5153.664 t=      302 R=   2e+05
Depth=    2552 States=  6.8e+07 Transitions= 1.34e+08 Memory=  5219.468 t=      307 R=   2e+05
Depth=    2552 States=  6.9e+07 Transitions= 1.36e+08 Memory=  5286.702 t=      311 R=   2e+05
Depth=    2552 States=    7e+07 Transitions= 1.38e+08 Memory=  5352.506 t=      316 R=   2e+05
Depth=    2552 States=  7.1e+07 Transitions=  1.4e+08 Memory=  5420.216 t=      320 R=   2e+05
Depth=    2552 States=  7.2e+07 Transitions= 1.42e+08 Memory=  5487.450 t=      325 R=   2e+05
Depth=    2552 States=  7.3e+07 Transitions= 1.44e+08 Memory=  5555.161 t=      330 R=   2e+05
Depth=    2552 States=  7.4e+07 Transitions= 1.46e+08 Memory=  5620.965 t=      334 R=   2e+05
Depth=    2552 States=  7.5e+07 Transitions= 1.48e+08 Memory=  5683.431 t=      339 R=   2e+05
Depth=    2552 States=  7.6e+07 Transitions=  1.5e+08 Memory=  5746.850 t=      343 R=   2e+05
Depth=    2552 States=  7.7e+07 Transitions= 1.52e+08 Memory=  5809.316 t=      348 R=   2e+05
Depth=    2552 States=  7.8e+07 Transitions= 1.54e+08 Memory=  5872.258 t=      352 R=   2e+05
Depth=    2552 States=  7.9e+07 Transitions= 1.56e+08 Memory=  5936.154 t=      357 R=   2e+05
Depth=    2552 States=    8e+07 Transitions= 1.57e+08 Memory=  6000.527 t=      361 R=   2e+05
Depth=    2552 States=  8.1e+07 Transitions= 1.59e+08 Memory=  6064.900 t=      366 R=   2e+05
Depth=    2552 States=  8.2e+07 Transitions= 1.61e+08 Memory=  6127.366 t=      370 R=   2e+05
Depth=    2552 States=  8.3e+07 Transitions= 1.63e+08 Memory=  6189.832 t=      375 R=   2e+05
Depth=    2552 States=  8.4e+07 Transitions= 1.65e+08 Memory=  6253.251 t=      379 R=   2e+05
Depth=    2552 States=  8.5e+07 Transitions= 1.67e+08 Memory=  6317.624 t=      384 R=   2e+05
Depth=    2552 States=  8.6e+07 Transitions= 1.69e+08 Memory=  6384.381 t=      389 R=   2e+05
Depth=    2552 States=  8.7e+07 Transitions= 1.71e+08 Memory=  6451.138 t=      393 R=   2e+05
Depth=    2552 States=  8.8e+07 Transitions= 1.73e+08 Memory=  6518.849 t=      398 R=   2e+05
Depth=    2552 States=  8.9e+07 Transitions= 1.75e+08 Memory=  6583.699 t=      402 R=   2e+05
Depth=    2552 States=    9e+07 Transitions= 1.77e+08 Memory=  6648.072 t=      407 R=   2e+05
Depth=    2552 States=  9.1e+07 Transitions= 1.79e+08 Memory=  6711.968 t=      412 R=   2e+05
Depth=    2552 States=  9.2e+07 Transitions= 1.81e+08 Memory=  6781.586 t=      416 R=   2e+05
Depth=    2552 States=  9.3e+07 Transitions= 1.83e+08 Memory=  6847.867 t=      421 R=   2e+05
Depth=    2552 States=  9.4e+07 Transitions= 1.85e+08 Memory=  6916.531 t=      426 R=   2e+05
Depth=    2552 States=  9.5e+07 Transitions= 1.87e+08 Memory=  6981.381 t=      430 R=   2e+05
Depth=    2552 States=  9.6e+07 Transitions= 1.89e+08 Memory=  7047.662 t=      435 R=   2e+05
Depth=    2552 States=  9.7e+07 Transitions= 1.91e+08 Memory=  7112.035 t=      439 R=   2e+05
Depth=    2552 States=  9.8e+07 Transitions= 1.93e+08 Memory=  7178.315 t=      444 R=   2e+05
Depth=    2552 States=  9.9e+07 Transitions= 1.95e+08 Memory=  7244.119 t=      449 R=   2e+05
Depth=    2552 States=    1e+08 Transitions= 1.97e+08 Memory=  7310.399 t=      453 R=   2e+05
Depth=    2552 States= 1.01e+08 Transitions= 1.99e+08 Memory=  7372.388 t=      458 R=   2e+05
Depth=    2552 States= 1.02e+08 Transitions= 2.01e+08 Memory=  7435.807 t=      463 R=   2e+05
Depth=    2552 States= 1.03e+08 Transitions= 2.03e+08 Memory=  7503.518 t=      467 R=   2e+05
Depth=    2552 States= 1.04e+08 Transitions= 2.05e+08 Memory=  7572.182 t=      472 R=   2e+05
Depth=    2552 States= 1.05e+08 Transitions= 2.07e+08 Memory=  7639.417 t=      477 R=   2e+05
Depth=    2552 States= 1.06e+08 Transitions= 2.09e+08 Memory=  7707.127 t=      481 R=   2e+05
Depth=    2552 States= 1.07e+08 Transitions= 2.11e+08 Memory=  7773.408 t=      486 R=   2e+05
Depth=    2552 States= 1.08e+08 Transitions= 2.13e+08 Memory=  7837.781 t=      490 R=   2e+05
Depth=    2552 States= 1.09e+08 Transitions= 2.15e+08 Memory=  7900.246 t=      495 R=   2e+05
Depth=    2552 States=  1.1e+08 Transitions= 2.17e+08 Memory=  7962.712 t=      500 R=   2e+05
Depth=    2552 States= 1.11e+08 Transitions= 2.18e+08 Memory=  8028.039 t=      504 R=   2e+05
Depth=    2552 States= 1.12e+08 Transitions=  2.2e+08 Memory=  8094.319 t=      509 R=   2e+05
Depth=    2552 States= 1.13e+08 Transitions= 2.22e+08 Memory=  8158.692 t=      514 R=   2e+05
Depth=    2552 States= 1.14e+08 Transitions= 2.24e+08 Memory=  8224.019 t=      518 R=   2e+05
Depth=    2552 States= 1.15e+08 Transitions= 2.26e+08 Memory=  8291.730 t=      523 R=   2e+05
Depth=    2552 States= 1.16e+08 Transitions= 2.28e+08 Memory=  8354.195 t=      527 R=   2e+05
Depth=    2552 States= 1.17e+08 Transitions=  2.3e+08 Memory=  8425.244 t=      532 R=   2e+05
Depth=    2552 States= 1.18e+08 Transitions= 2.32e+08 Memory=  8494.862 t=      537 R=   2e+05
Depth=    2552 States= 1.19e+08 Transitions= 2.34e+08 Memory=  8562.096 t=      541 R=   2e+05
Depth=    2552 States=  1.2e+08 Transitions= 2.36e+08 Memory=  8632.191 t=      546 R=   2e+05
Depth=    2552 States= 1.21e+08 Transitions= 2.38e+08 Memory=  8699.426 t=      551 R=   2e+05
Depth=    2552 States= 1.22e+08 Transitions=  2.4e+08 Memory=  8765.706 t=      556 R=   2e+05
Depth=    2552 States= 1.23e+08 Transitions= 2.42e+08 Memory=  8833.417 t=      561 R=   2e+05
Depth=    2552 States= 1.24e+08 Transitions= 2.44e+08 Memory=  8901.128 t=      565 R=   2e+05
Depth=    2552 States= 1.25e+08 Transitions= 2.46e+08 Memory=  8966.931 t=      570 R=   2e+05
Depth=    2552 States= 1.26e+08 Transitions= 2.48e+08 Memory=  9033.688 t=      575 R=   2e+05
Depth=    2552 States= 1.27e+08 Transitions=  2.5e+08 Memory=  9096.631 t=      580 R=   2e+05
Depth=    2552 States= 1.28e+08 Transitions= 2.52e+08 Memory=  9159.573 t=      584 R=   2e+05
Depth=    2552 States= 1.29e+08 Transitions= 2.54e+08 Memory=  9221.085 t=      589 R=   2e+05
Depth=    2552 States=  1.3e+08 Transitions= 2.56e+08 Memory=  9286.412 t=      594 R=   2e+05
Depth=    2552 States= 1.31e+08 Transitions= 2.58e+08 Memory=  9350.785 t=      599 R=   2e+05
Depth=    2552 States= 1.32e+08 Transitions=  2.6e+08 Memory=  9416.112 t=      604 R=   2e+05
Depth=    2552 States= 1.33e+08 Transitions= 2.62e+08 Memory=  9479.531 t=      608 R=   2e+05
Depth=    2552 States= 1.34e+08 Transitions= 2.64e+08 Memory=  9545.811 t=      613 R=   2e+05
Depth=    2552 States= 1.35e+08 Transitions= 2.66e+08 Memory=  9608.277 t=      618 R=   2e+05
pan: resizing hashtable to -w28..  done
Depth=    2552 States= 1.36e+08 Transitions= 2.68e+08 Memory= 11665.814 t=      648 R=   2e+05
Depth=    2552 States= 1.37e+08 Transitions=  2.7e+08 Memory= 11734.002 t=      652 R=   2e+05
Depth=    2552 States= 1.38e+08 Transitions= 2.72e+08 Memory= 11800.282 t=      656 R=   2e+05
Depth=    2552 States= 1.39e+08 Transitions= 2.74e+08 Memory= 11864.178 t=      661 R=   2e+05
Depth=    2552 States=  1.4e+08 Transitions= 2.76e+08 Memory= 11929.505 t=      665 R=   2e+05
Depth=    2552 States= 1.41e+08 Transitions= 2.78e+08 Memory= 11995.308 t=      670 R=   2e+05
Depth=    2552 States= 1.42e+08 Transitions=  2.8e+08 Memory= 12060.158 t=      674 R=   2e+05
Depth=    2552 States= 1.43e+08 Transitions= 2.82e+08 Memory= 12124.054 t=      679 R=   2e+05
Depth=    2552 States= 1.44e+08 Transitions= 2.84e+08 Memory= 12186.997 t=      683 R=   2e+05
Depth=    2552 States= 1.45e+08 Transitions= 2.86e+08 Memory= 12257.569 t=      687 R=   2e+05
Depth=    2552 States= 1.46e+08 Transitions= 2.88e+08 Memory= 12328.141 t=      692 R=   2e+05
Depth=    2552 States= 1.47e+08 Transitions=  2.9e+08 Memory= 12398.713 t=      696 R=   2e+05
Depth=    2552 States= 1.48e+08 Transitions= 2.92e+08 Memory= 12467.377 t=      701 R=   2e+05
Depth=    2552 States= 1.49e+08 Transitions= 2.94e+08 Memory= 12536.042 t=      705 R=   2e+05
Depth=    2552 States=  1.5e+08 Transitions= 2.96e+08 Memory= 12604.706 t=      710 R=   2e+05
Depth=    2552 States= 1.51e+08 Transitions= 2.98e+08 Memory= 12673.371 t=      714 R=   2e+05
Depth=    2552 States= 1.52e+08 Transitions=    3e+08 Memory= 12743.466 t=      719 R=   2e+05
Depth=    2552 States= 1.53e+08 Transitions= 3.01e+08 Memory= 12812.130 t=      723 R=   2e+05
Depth=    2552 States= 1.54e+08 Transitions= 3.03e+08 Memory= 12880.795 t=      728 R=   2e+05
Depth=    2552 States= 1.55e+08 Transitions= 3.05e+08 Memory= 12952.321 t=      732 R=   2e+05
Depth=    2552 States= 1.56e+08 Transitions= 3.07e+08 Memory= 13023.369 t=      737 R=   2e+05
Depth=    2552 States= 1.57e+08 Transitions= 3.09e+08 Memory= 13092.034 t=      741 R=   2e+05
Depth=    2552 States= 1.58e+08 Transitions= 3.11e+08 Memory= 13161.175 t=      745 R=   2e+05
Depth=    2552 States= 1.59e+08 Transitions= 3.13e+08 Memory= 13229.840 t=      750 R=   2e+05
Depth=    2552 States=  1.6e+08 Transitions= 3.15e+08 Memory= 13299.935 t=      754 R=   2e+05
Depth=    2552 States= 1.61e+08 Transitions= 3.17e+08 Memory= 13368.123 t=      759 R=   2e+05
Depth=    2552 States= 1.62e+08 Transitions= 3.19e+08 Memory= 13439.171 t=      763 R=   2e+05
Depth=    2552 States= 1.63e+08 Transitions= 3.21e+08 Memory= 13509.743 t=      768 R=   2e+05
Depth=    2552 States= 1.64e+08 Transitions= 3.23e+08 Memory= 13580.315 t=      772 R=   2e+05
Depth=    2552 States= 1.65e+08 Transitions= 3.25e+08 Memory= 13648.980 t=      777 R=   2e+05
Depth=    2552 States= 1.66e+08 Transitions= 3.27e+08 Memory= 13717.644 t=      781 R=   2e+05
Depth=    2552 States= 1.67e+08 Transitions= 3.29e+08 Memory= 13786.309 t=      786 R=   2e+05
Depth=    2552 States= 1.68e+08 Transitions= 3.31e+08 Memory= 13856.404 t=      791 R=   2e+05
Depth=    2552 States= 1.69e+08 Transitions= 3.33e+08 Memory= 13925.068 t=      795 R=   2e+05
Depth=    2552 States=  1.7e+08 Transitions= 3.35e+08 Memory= 13994.687 t=      800 R=   2e+05
Depth=    2552 States= 1.71e+08 Transitions= 3.37e+08 Memory= 14064.305 t=      804 R=   2e+05
Depth=    2552 States= 1.72e+08 Transitions= 3.39e+08 Memory= 14135.354 t=      809 R=   2e+05
Depth=    2552 States= 1.73e+08 Transitions= 3.41e+08 Memory= 14201.634 t=      813 R=   2e+05
Depth=    2552 States= 1.74e+08 Transitions= 3.43e+08 Memory= 14269.822 t=      817 R=   2e+05
Depth=    2552 States= 1.75e+08 Transitions= 3.45e+08 Memory= 14340.394 t=      822 R=   2e+05
Depth=    2552 States= 1.76e+08 Transitions= 3.47e+08 Memory= 14409.058 t=      826 R=   2e+05
Depth=    2552 States= 1.77e+08 Transitions= 3.49e+08 Memory= 14480.584 t=      831 R=   2e+05
Depth=    2552 States= 1.78e+08 Transitions= 3.51e+08 Memory= 14550.202 t=      835 R=   2e+05
Depth=    2552 States= 1.79e+08 Transitions= 3.53e+08 Memory= 14621.251 t=      840 R=   2e+05
Depth=    2552 States=  1.8e+08 Transitions= 3.55e+08 Memory= 14690.392 t=      844 R=   2e+05
Depth=    2552 States= 1.81e+08 Transitions= 3.57e+08 Memory= 14761.918 t=      849 R=   2e+05
Depth=    2552 States= 1.82e+08 Transitions= 3.59e+08 Memory= 14833.920 t=      853 R=   2e+05
Depth=    2552 States= 1.83e+08 Transitions= 3.61e+08 Memory= 14904.969 t=      858 R=   2e+05
Depth=    2552 States= 1.84e+08 Transitions= 3.63e+08 Memory= 14972.680 t=      862 R=   2e+05
Depth=    2552 States= 1.85e+08 Transitions= 3.65e+08 Memory= 15047.066 t=      867 R=   2e+05
Depth=    2552 States= 1.86e+08 Transitions= 3.67e+08 Memory= 15120.022 t=      871 R=   2e+05
Depth=    2552 States= 1.87e+08 Transitions= 3.68e+08 Memory= 15192.025 t=      876 R=   2e+05
Depth=    2552 States= 1.88e+08 Transitions=  3.7e+08 Memory= 15265.934 t=      880 R=   2e+05
Depth=    2552 States= 1.89e+08 Transitions= 3.72e+08 Memory= 15337.937 t=      885 R=   2e+05
Depth=    2552 States=  1.9e+08 Transitions= 3.74e+08 Memory= 15407.555 t=      889 R=   2e+05
Depth=    2552 States= 1.91e+08 Transitions= 3.76e+08 Memory= 15477.650 t=      894 R=   2e+05
Depth=    2552 States= 1.92e+08 Transitions= 3.78e+08 Memory= 15549.176 t=      898 R=   2e+05
Depth=    2552 States= 1.93e+08 Transitions=  3.8e+08 Memory= 15621.178 t=      903 R=   2e+05
Depth=    2552 States= 1.94e+08 Transitions= 3.82e+08 Memory= 15692.704 t=      907 R=   2e+05
Depth=    2552 States= 1.95e+08 Transitions= 3.84e+08 Memory= 15762.799 t=      912 R=   2e+05
Depth=    2552 States= 1.96e+08 Transitions= 3.86e+08 Memory= 15833.848 t=      916 R=   2e+05
Depth=    2552 States= 1.97e+08 Transitions= 3.88e+08 Memory= 15907.280 t=      921 R=   2e+05
Depth=    2552 States= 1.98e+08 Transitions=  3.9e+08 Memory= 15977.375 t=      925 R=   2e+05
Depth=    2552 States= 1.99e+08 Transitions= 3.92e+08 Memory= 16046.040 t=      930 R=   2e+05
Depth=    2552 States=    2e+08 Transitions= 3.94e+08 Memory= 16120.427 t=      934 R=   2e+05
Depth=    2552 States= 2.01e+08 Transitions= 3.96e+08 Memory= 16192.906 t=      939 R=   2e+05
Depth=    2552 States= 2.02e+08 Transitions= 3.98e+08 Memory= 16265.385 t=      943 R=   2e+05
Depth=    2552 States= 2.03e+08 Transitions=    4e+08 Memory= 16337.864 t=      948 R=   2e+05
Depth=    2552 States= 2.04e+08 Transitions= 4.02e+08 Memory= 16409.867 t=      952 R=   2e+05
Depth=    2552 States= 2.05e+08 Transitions= 4.04e+08 Memory= 16483.777 t=      957 R=   2e+05
Depth=    2552 States= 2.06e+08 Transitions= 4.06e+08 Memory= 16557.209 t=      961 R=   2e+05
Depth=    2552 States= 2.07e+08 Transitions= 4.08e+08 Memory= 16629.212 t=      966 R=   2e+05
Depth=    2552 States= 2.08e+08 Transitions=  4.1e+08 Memory= 16699.784 t=      970 R=   2e+05
Depth=    2552 States= 2.09e+08 Transitions= 4.12e+08 Memory= 16769.402 t=      975 R=   2e+05
Depth=    2552 States=  2.1e+08 Transitions= 4.14e+08 Memory= 16838.067 t=      979 R=   2e+05
Depth=    2552 States= 2.11e+08 Transitions= 4.16e+08 Memory= 16906.731 t=      984 R=   2e+05
Depth=    2552 States= 2.12e+08 Transitions= 4.18e+08 Memory= 16975.396 t=      988 R=   2e+05
Depth=    2552 States= 2.13e+08 Transitions=  4.2e+08 Memory= 17043.583 t=      993 R=   2e+05
Depth=    2552 States= 2.14e+08 Transitions= 4.22e+08 Memory= 17113.678 t=      997 R=   2e+05
Depth=    2552 States= 2.15e+08 Transitions= 4.24e+08 Memory= 17185.681 t=    1e+03 R=   2e+05
Depth=    2552 States= 2.16e+08 Transitions= 4.26e+08 Memory= 17256.253 t= 1.01e+03 R=   2e+05
Depth=    2552 States= 2.17e+08 Transitions= 4.27e+08 Memory= 17324.917 t= 1.01e+03 R=   2e+05
Depth=    2552 States= 2.18e+08 Transitions= 4.29e+08 Memory= 17393.582 t= 1.02e+03 R=   2e+05
Depth=    2552 States= 2.19e+08 Transitions= 4.31e+08 Memory= 17462.246 t= 1.02e+03 R=   2e+05
Depth=    2552 States=  2.2e+08 Transitions= 4.33e+08 Memory= 17530.911 t= 1.02e+03 R=   2e+05
Depth=    2552 States= 2.21e+08 Transitions= 4.35e+08 Memory= 17601.960 t= 1.03e+03 R=   2e+05
Depth=    2552 States= 2.22e+08 Transitions= 4.37e+08 Memory= 17675.869 t= 1.03e+03 R=   2e+05
Depth=    2552 States= 2.23e+08 Transitions= 4.39e+08 Memory= 17748.826 t= 1.04e+03 R=   2e+05
Depth=    2552 States= 2.24e+08 Transitions= 4.41e+08 Memory= 17818.921 t= 1.04e+03 R=   2e+05
Depth=    2552 States= 2.25e+08 Transitions= 4.43e+08 Memory= 17888.062 t= 1.05e+03 R=   2e+05
Depth=    2552 States= 2.26e+08 Transitions= 4.45e+08 Memory= 17956.727 t= 1.05e+03 R=   2e+05
Depth=    2552 States= 2.27e+08 Transitions= 4.47e+08 Memory= 18028.252 t= 1.06e+03 R=   2e+05
Depth=    2552 States= 2.28e+08 Transitions= 4.49e+08 Memory= 18098.347 t= 1.06e+03 R=   2e+05
Depth=    2552 States= 2.29e+08 Transitions= 4.51e+08 Memory= 18167.012 t= 1.07e+03 R=   2e+05
Depth=    2552 States=  2.3e+08 Transitions= 4.53e+08 Memory= 18236.630 t= 1.07e+03 R=   2e+05
Depth=    2552 States= 2.31e+08 Transitions= 4.55e+08 Memory= 18308.156 t= 1.07e+03 R=   2e+05
Depth=    2552 States= 2.32e+08 Transitions= 4.57e+08 Memory= 18377.297 t= 1.08e+03 R=   2e+05
Depth=    2552 States= 2.33e+08 Transitions= 4.59e+08 Memory= 18449.299 t= 1.08e+03 R=   2e+05
Depth=    2552 States= 2.34e+08 Transitions= 4.61e+08 Memory= 18521.779 t= 1.09e+03 R=   2e+05
Depth=    2552 States= 2.35e+08 Transitions= 4.63e+08 Memory= 18592.827 t= 1.09e+03 R=   2e+05
Depth=    2552 States= 2.36e+08 Transitions= 4.65e+08 Memory= 18662.922 t=  1.1e+03 R=   2e+05
Depth=    2552 States= 2.37e+08 Transitions= 4.67e+08 Memory= 18733.971 t=  1.1e+03 R=   2e+05
Depth=    2552 States= 2.38e+08 Transitions= 4.69e+08 Memory= 18805.974 t= 1.11e+03 R=   2e+05
Depth=    2552 States= 2.39e+08 Transitions= 4.71e+08 Memory= 18878.453 t= 1.11e+03 R=   2e+05
Depth=    2552 States=  2.4e+08 Transitions= 4.73e+08 Memory= 18952.839 t= 1.12e+03 R=   2e+05
Depth=    2552 States= 2.41e+08 Transitions= 4.75e+08 Memory= 19025.795 t= 1.12e+03 R=   2e+05
Depth=    2552 States= 2.42e+08 Transitions= 4.77e+08 Memory= 19097.798 t= 1.12e+03 R=   2e+05
Depth=    2552 States= 2.43e+08 Transitions= 4.79e+08 Memory= 19168.847 t= 1.13e+03 R=   2e+05
Depth=    2552 States= 2.44e+08 Transitions= 4.81e+08 Memory= 19236.557 t= 1.13e+03 R=   2e+05
Depth=    2552 States= 2.45e+08 Transitions= 4.83e+08 Memory= 19304.745 t= 1.14e+03 R=   2e+05
Depth=    2552 States= 2.46e+08 Transitions= 4.85e+08 Memory= 19372.456 t= 1.14e+03 R=   2e+05
Depth=    2552 States= 2.47e+08 Transitions= 4.87e+08 Memory= 19442.074 t= 1.15e+03 R=   2e+05
Depth=    2552 States= 2.48e+08 Transitions= 4.88e+08 Memory= 19509.308 t= 1.15e+03 R=   2e+05
Depth=    2552 States= 2.49e+08 Transitions=  4.9e+08 Memory= 19579.880 t= 1.16e+03 R=   2e+05
Depth=    2552 States=  2.5e+08 Transitions= 4.92e+08 Memory= 19651.406 t= 1.16e+03 R=   2e+05
Depth=    2552 States= 2.51e+08 Transitions= 4.94e+08 Memory= 19721.024 t= 1.17e+03 R=   2e+05
Depth=    2552 States= 2.52e+08 Transitions= 4.96e+08 Memory= 19792.073 t= 1.17e+03 R=   2e+05
Depth=    2552 States= 2.53e+08 Transitions= 4.98e+08 Memory= 19863.121 t= 1.17e+03 R=   2e+05
Depth=    2552 States= 2.54e+08 Transitions=    5e+08 Memory= 19934.647 t= 1.18e+03 R=   2e+05
Depth=    2552 States= 2.55e+08 Transitions= 5.02e+08 Memory= 20008.080 t= 1.18e+03 R=   2e+05
Depth=    2552 States= 2.56e+08 Transitions= 5.04e+08 Memory= 20081.036 t= 1.19e+03 R=   2e+05
Depth=    2552 States= 2.57e+08 Transitions= 5.06e+08 Memory= 20154.946 t= 1.19e+03 R=   2e+05
Depth=    2552 States= 2.58e+08 Transitions= 5.08e+08 Memory= 20230.286 t=  1.2e+03 R=   2e+05
Depth=    2552 States= 2.59e+08 Transitions=  5.1e+08 Memory= 20304.196 t=  1.2e+03 R=   2e+05
Depth=    2552 States=  2.6e+08 Transitions= 5.12e+08 Memory= 20380.013 t= 1.21e+03 R=   2e+05
Depth=    2552 States= 2.61e+08 Transitions= 5.14e+08 Memory= 20454.876 t= 1.21e+03 R=   2e+05
Depth=    2552 States= 2.62e+08 Transitions= 5.16e+08 Memory= 20524.018 t= 1.22e+03 R=   2e+05
Depth=    2552 States= 2.63e+08 Transitions= 5.18e+08 Memory= 20595.543 t= 1.22e+03 R=   2e+05
Depth=    2552 States= 2.64e+08 Transitions=  5.2e+08 Memory= 20663.731 t= 1.22e+03 R=   2e+05
Depth=    2552 States= 2.65e+08 Transitions= 5.22e+08 Memory= 20738.118 t= 1.23e+03 R=   2e+05
Depth=    2552 States= 2.66e+08 Transitions= 5.24e+08 Memory= 20809.166 t= 1.23e+03 R=   2e+05
Depth=    2552 States= 2.67e+08 Transitions= 5.26e+08 Memory= 20882.122 t= 1.24e+03 R=   2e+05
Depth=    2552 States= 2.68e+08 Transitions= 5.28e+08 Memory= 20954.602 t= 1.24e+03 R=   2e+05
Depth=    2552 States= 2.69e+08 Transitions=  5.3e+08 Memory= 21028.988 t= 1.25e+03 R=   2e+05
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
