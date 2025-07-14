# Preemptive fixed-priority scheduler that ensures priorities

This is a model of the fully-preemptive `PrioritizedFIFOScheduler` to verify that priority inversion does not occur.
Note that this does not consider inter-scheduler preemption.
We have prepared an environment that could cause the priority inversion presented in [this comments](https://github.com/tier4/awkernel/pull/255#issuecomment-2556669740).
There are two CPUs and five tasks, and the smaller the task index, the higher the priority.
Tasks are executed as follows:

1. init: wake task 4
2. (CPU 0) worker thread 0: execute task 4, wake task 3, and block.
3. (CPU 1) worker thread 1: execute task 3, wake tasks 0,1,2, send IPI for preemption, and block.
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
gcc -O3 -DCOLLAPSE -DVECTORSZ=5000 -DNFAIR=3 -o pan pan.c
rm -f *.trail
./pan -a -n -m60000
Depth=    2672 States=    1e+06 Transitions= 2.36e+06 Memory=   168.856 t=     7.35 R=   1e+05
Depth=    2672 States=    2e+06 Transitions= 4.74e+06 Memory=   201.757 t=     14.7 R=   1e+05
Depth=    2672 States=    3e+06 Transitions= 7.12e+06 Memory=   236.566 t=     22.1 R=   1e+05
Depth=    2961 States=    4e+06 Transitions= 9.49e+06 Memory=   268.515 t=     29.4 R=   1e+05
Depth=    2961 States=    5e+06 Transitions= 1.19e+07 Memory=   299.986 t=     36.8 R=   1e+05
Depth=    3165 States=    6e+06 Transitions= 1.42e+07 Memory=   335.749 t=     44.2 R=   1e+05
Depth=    3165 States=    7e+06 Transitions= 1.66e+07 Memory=   371.988 t=     51.6 R=   1e+05
Depth=    3165 States=    8e+06 Transitions=  1.9e+07 Memory=   406.320 t=     59.2 R=   1e+05
Depth=    3168 States=    9e+06 Transitions= 2.13e+07 Memory=   441.130 t=     66.6 R=   1e+05
Depth=    3168 States=    1e+07 Transitions= 2.37e+07 Memory=   476.416 t=       74 R=   1e+05
Depth=    3168 States=  1.1e+07 Transitions= 2.61e+07 Memory=   511.702 t=     81.6 R=   1e+05
Depth=    3168 States=  1.2e+07 Transitions= 2.84e+07 Memory=   546.511 t=     89.1 R=   1e+05
Depth=    3168 States=  1.3e+07 Transitions= 3.08e+07 Memory=   580.366 t=     96.6 R=   1e+05
Depth=    3168 States=  1.4e+07 Transitions= 3.32e+07 Memory=   615.175 t=      104 R=   1e+05
Depth=    3168 States=  1.5e+07 Transitions= 3.56e+07 Memory=   648.077 t=      112 R=   1e+05
Depth=    3168 States=  1.6e+07 Transitions=  3.8e+07 Memory=   679.071 t=      119 R=   1e+05
Depth=    3168 States=  1.7e+07 Transitions= 4.03e+07 Memory=   709.589 t=      127 R=   1e+05
Depth=    3168 States=  1.8e+07 Transitions= 4.27e+07 Memory=   740.107 t=      134 R=   1e+05
Depth=    3168 States=  1.9e+07 Transitions= 4.51e+07 Memory=   773.008 t=      142 R=   1e+05
Depth=    3168 States=    2e+07 Transitions= 4.74e+07 Memory=   807.341 t=      149 R=   1e+05
Depth=    3168 States=  2.1e+07 Transitions= 4.98e+07 Memory=   841.196 t=      157 R=   1e+05
Depth=    3168 States=  2.2e+07 Transitions= 5.22e+07 Memory=   875.528 t=      164 R=   1e+05
Depth=    3168 States=  2.3e+07 Transitions= 5.45e+07 Memory=   909.861 t=      172 R=   1e+05
Depth=    3168 States=  2.4e+07 Transitions= 5.69e+07 Memory=   944.193 t=      179 R=   1e+05
Depth=    3168 States=  2.5e+07 Transitions= 5.93e+07 Memory=   980.432 t=      187 R=   1e+05
Depth=    3168 States=  2.6e+07 Transitions= 6.17e+07 Memory=  1016.195 t=      195 R=   1e+05
Depth=    3168 States=  2.7e+07 Transitions= 6.41e+07 Memory=  1050.051 t=      202 R=   1e+05
Depth=    3168 States=  2.8e+07 Transitions= 6.64e+07 Memory=  1081.522 t=      210 R=   1e+05
Depth=    3168 States=  2.9e+07 Transitions= 6.88e+07 Memory=  1112.993 t=      218 R=   1e+05
Depth=    3168 States=    3e+07 Transitions= 7.12e+07 Memory=  1144.941 t=      225 R=   1e+05
Depth=    3168 States=  3.1e+07 Transitions= 7.36e+07 Memory=  1178.797 t=      233 R=   1e+05
Depth=    3168 States=  3.2e+07 Transitions= 7.61e+07 Memory=  1212.652 t=      241 R=   1e+05
Depth=    3168 States=  3.3e+07 Transitions= 7.85e+07 Memory=  1244.600 t=      249 R=   1e+05
Depth=    3168 States=  3.4e+07 Transitions= 8.09e+07 Memory=  1277.502 t=      257 R=   1e+05
pan: resizing hashtable to -w26..  done
Depth=    3168 States=  3.5e+07 Transitions= 8.34e+07 Memory=  1805.714 t=      267 R=   1e+05
Depth=    3168 States=  3.6e+07 Transitions= 8.58e+07 Memory=  1836.709 t=      275 R=   1e+05
Depth=    3168 States=  3.7e+07 Transitions= 8.82e+07 Memory=  1875.333 t=      283 R=   1e+05
Depth=    3168 States=  3.8e+07 Transitions= 9.07e+07 Memory=  1909.665 t=      290 R=   1e+05
Depth=    3168 States=  3.9e+07 Transitions= 9.31e+07 Memory=  1943.997 t=      298 R=   1e+05
Depth=    3168 States=    4e+07 Transitions= 9.55e+07 Memory=  1978.329 t=      306 R=   1e+05
Depth=    3169 States=  4.1e+07 Transitions=  9.8e+07 Memory=  2013.615 t=      313 R=   1e+05
Depth=    3169 States=  4.2e+07 Transitions=    1e+08 Memory=  2047.948 t=      321 R=   1e+05
Depth=    3169 States=  4.3e+07 Transitions= 1.03e+08 Memory=  2082.280 t=      329 R=   1e+05
Depth=    3169 States=  4.4e+07 Transitions= 1.05e+08 Memory=  2116.135 t=      337 R=   1e+05
Depth=    3169 States=  4.5e+07 Transitions= 1.08e+08 Memory=  2149.991 t=      345 R=   1e+05
Depth=    3169 States=  4.6e+07 Transitions=  1.1e+08 Memory=  2183.846 t=      353 R=   1e+05
Depth=    3169 States=  4.7e+07 Transitions= 1.13e+08 Memory=  2217.702 t=      361 R=   1e+05
Depth=    3169 States=  4.8e+07 Transitions= 1.15e+08 Memory=  2249.650 t=      369 R=   1e+05
Depth=    3169 States=  4.9e+07 Transitions= 1.17e+08 Memory=  2280.167 t=      377 R=   1e+05
Depth=    3169 States=    5e+07 Transitions=  1.2e+08 Memory=  2310.685 t=      385 R=   1e+05
Depth=    3169 States=  5.1e+07 Transitions= 1.22e+08 Memory=  2341.203 t=      393 R=   1e+05
Depth=    3169 States=  5.2e+07 Transitions= 1.25e+08 Memory=  2375.058 t=      401 R=   1e+05
Depth=    3169 States=  5.3e+07 Transitions= 1.27e+08 Memory=  2408.913 t=      409 R=   1e+05
Depth=    3169 States=  5.4e+07 Transitions=  1.3e+08 Memory=  2443.246 t=      417 R=   1e+05
Depth=    3169 States=  5.5e+07 Transitions= 1.32e+08 Memory=  2477.101 t=      425 R=   1e+05
Depth=    3169 States=  5.6e+07 Transitions= 1.35e+08 Memory=  2511.433 t=      433 R=   1e+05
Depth=    3169 States=  5.7e+07 Transitions= 1.37e+08 Memory=  2545.289 t=      440 R=   1e+05
Depth=    3169 States=  5.8e+07 Transitions= 1.39e+08 Memory=  2578.667 t=      448 R=   1e+05
Depth=    3169 States=  5.9e+07 Transitions= 1.42e+08 Memory=  2613.477 t=      456 R=   1e+05
Depth=    3169 States=    6e+07 Transitions= 1.44e+08 Memory=  2650.193 t=      464 R=   1e+05
Depth=    3169 States=  6.1e+07 Transitions= 1.47e+08 Memory=  2684.048 t=      472 R=   1e+05
Depth=    3169 States=  6.2e+07 Transitions= 1.49e+08 Memory=  2718.381 t=      479 R=   1e+05
Depth=    3169 States=  6.3e+07 Transitions= 1.52e+08 Memory=  2749.852 t=      487 R=   1e+05
Depth=    3169 States=  6.4e+07 Transitions= 1.54e+08 Memory=  2781.800 t=      495 R=   1e+05
Depth=    3169 States=  6.5e+07 Transitions= 1.56e+08 Memory=  2813.271 t=      503 R=   1e+05
Depth=    3169 States=  6.6e+07 Transitions= 1.59e+08 Memory=  2859.048 t=      510 R=   1e+05
Depth=    3169 States=  6.7e+07 Transitions= 1.61e+08 Memory=  2924.851 t=      518 R=   1e+05
Depth=    3169 States=  6.8e+07 Transitions= 1.63e+08 Memory=  2991.608 t=      525 R=   1e+05
Depth=    3169 States=  6.9e+07 Transitions= 1.66e+08 Memory=  3054.074 t=      536 R=   1e+05
Depth=    3169 States=    7e+07 Transitions= 1.69e+08 Memory=  3118.924 t=      543 R=   1e+05
Depth=    3169 States=  7.1e+07 Transitions= 1.72e+08 Memory=  3181.866 t=      553 R=   1e+05
Depth=    3169 States=  7.2e+07 Transitions= 1.74e+08 Memory=  3245.763 t=      561 R=   1e+05
Depth=    3169 States=  7.3e+07 Transitions= 1.77e+08 Memory=  3308.705 t=      571 R=   1e+05
Depth=    3169 States=  7.4e+07 Transitions= 1.79e+08 Memory=  3371.648 t=      580 R=   1e+05
Depth=    3257 States=  7.5e+07 Transitions= 1.82e+08 Memory=  3439.835 t=      588 R=   1e+05
Depth=    3257 States=  7.6e+07 Transitions= 1.84e+08 Memory=  3510.884 t=      597 R=   1e+05
Depth=    3257 States=  7.7e+07 Transitions= 1.87e+08 Memory=  3579.072 t=      606 R=   1e+05
Depth=    3257 States=  7.8e+07 Transitions= 1.89e+08 Memory=  3647.260 t=      614 R=   1e+05
Depth=    3257 States=  7.9e+07 Transitions= 1.92e+08 Memory=  3715.924 t=      622 R=   1e+05
Depth=    3257 States=    8e+07 Transitions= 1.94e+08 Memory=  3784.589 t=      631 R=   1e+05
Depth=    3260 States=  8.1e+07 Transitions= 1.97e+08 Memory=  3852.776 t=      640 R=   1e+05
Depth=    3260 States=  8.2e+07 Transitions= 1.99e+08 Memory=  3921.441 t=      648 R=   1e+05
Depth=    3260 States=  8.3e+07 Transitions= 2.02e+08 Memory=  3990.105 t=      657 R=   1e+05
Depth=    3260 States=  8.4e+07 Transitions= 2.04e+08 Memory=  4058.770 t=      665 R=   1e+05
Depth=    3260 States=  8.5e+07 Transitions= 2.07e+08 Memory=  4126.958 t=      674 R=   1e+05
Depth=    3260 States=  8.6e+07 Transitions= 2.09e+08 Memory=  4194.669 t=      682 R=   1e+05
Depth=    3260 States=  8.7e+07 Transitions= 2.12e+08 Memory=  4262.856 t=      690 R=   1e+05
Depth=    3260 States=  8.8e+07 Transitions= 2.14e+08 Memory=  4331.521 t=      699 R=   1e+05
Depth=    3260 States=  8.9e+07 Transitions= 2.17e+08 Memory=  4398.755 t=      709 R=   1e+05
Depth=    3260 States=    9e+07 Transitions=  2.2e+08 Memory=  4462.174 t=      717 R=   1e+05
Depth=    3260 States=  9.1e+07 Transitions= 2.22e+08 Memory=  4526.547 t=      724 R=   1e+05
Depth=    3260 States=  9.2e+07 Transitions= 2.25e+08 Memory=  4588.536 t=      735 R=   1e+05
Depth=    3260 States=  9.3e+07 Transitions= 2.27e+08 Memory=  4652.909 t=      742 R=   1e+05
Depth=    3260 States=  9.4e+07 Transitions=  2.3e+08 Memory=  4715.375 t=      753 R=   1e+05
Depth=    3260 States=  9.5e+07 Transitions= 2.33e+08 Memory=  4778.317 t=      762 R=   1e+05
Depth=    3260 States=  9.6e+07 Transitions= 2.35e+08 Memory=  4845.074 t=      770 R=   1e+05
Depth=    3260 States=  9.7e+07 Transitions= 2.38e+08 Memory=  4913.262 t=      779 R=   1e+05
Depth=    3260 States=  9.8e+07 Transitions=  2.4e+08 Memory=  4981.450 t=      787 R=   1e+05
Depth=    3260 States=  9.9e+07 Transitions= 2.43e+08 Memory=  5049.638 t=      796 R=   1e+05
Depth=    3260 States=    1e+08 Transitions= 2.45e+08 Memory=  5118.302 t=      804 R=   1e+05
Depth=    3260 States= 1.01e+08 Transitions= 2.48e+08 Memory=  5186.490 t=      813 R=   1e+05
Depth=    3260 States= 1.02e+08 Transitions=  2.5e+08 Memory=  5255.154 t=      821 R=   1e+05
Depth=    3260 States= 1.03e+08 Transitions= 2.53e+08 Memory=  5323.342 t=      830 R=   1e+05
Depth=    3260 States= 1.04e+08 Transitions= 2.55e+08 Memory=  5391.530 t=      838 R=   1e+05
Depth=    3260 States= 1.05e+08 Transitions= 2.58e+08 Memory=  5459.718 t=      847 R=   1e+05
Depth=    3260 States= 1.06e+08 Transitions= 2.61e+08 Memory=  5525.998 t=      856 R=   1e+05
Depth=    3260 States= 1.07e+08 Transitions= 2.63e+08 Memory=  5596.570 t=      865 R=   1e+05
Depth=    3260 States= 1.08e+08 Transitions= 2.65e+08 Memory=  5664.758 t=      873 R=   1e+05
Depth=    3260 States= 1.09e+08 Transitions= 2.68e+08 Memory=  5732.468 t=      883 R=   1e+05
Depth=    3260 States=  1.1e+08 Transitions= 2.71e+08 Memory=  5797.318 t=      891 R=   1e+05
Depth=    3260 States= 1.11e+08 Transitions= 2.73e+08 Memory=  5861.691 t=      899 R=   1e+05
Depth=    3260 States= 1.12e+08 Transitions= 2.76e+08 Memory=  5926.064 t=      909 R=   1e+05
Depth=    3260 States= 1.13e+08 Transitions= 2.79e+08 Memory=  5990.437 t=      917 R=   1e+05
Depth=    3260 States= 1.14e+08 Transitions= 2.81e+08 Memory=  6054.810 t=      926 R=   1e+05
Depth=    3260 States= 1.15e+08 Transitions= 2.84e+08 Memory=  6120.614 t=      935 R=   1e+05
Depth=    3260 States= 1.16e+08 Transitions= 2.87e+08 Memory=  6182.603 t=      948 R=   1e+05
Depth=    3260 States= 1.17e+08 Transitions= 2.91e+08 Memory=  6243.638 t=      961 R=   1e+05
Depth=    3260 States= 1.18e+08 Transitions= 2.95e+08 Memory=  6304.673 t=      974 R=   1e+05
Depth=    3260 States= 1.19e+08 Transitions= 2.99e+08 Memory=  6371.430 t=      988 R=   1e+05
Depth=    3260 States=  1.2e+08 Transitions= 3.03e+08 Memory=  6439.618 t=    1e+03 R=   1e+05
Depth=    3260 States= 1.21e+08 Transitions= 3.07e+08 Memory=  6507.329 t= 1.01e+03 R=   1e+05
Depth=    3260 States= 1.22e+08 Transitions= 3.11e+08 Memory=  6574.086 t= 1.03e+03 R=   1e+05
Depth=    3260 States= 1.23e+08 Transitions= 3.15e+08 Memory=  6641.797 t= 1.04e+03 R=   1e+05
Depth=    3260 States= 1.24e+08 Transitions= 3.19e+08 Memory=  6702.832 t= 1.05e+03 R=   1e+05
Depth=    3260 States= 1.25e+08 Transitions= 3.23e+08 Memory=  6763.867 t= 1.07e+03 R=   1e+05
Depth=    3260 States= 1.26e+08 Transitions= 3.27e+08 Memory=  6828.717 t= 1.08e+03 R=   1e+05
Depth=    3260 States= 1.27e+08 Transitions= 3.31e+08 Memory=  6896.428 t= 1.09e+03 R=   1e+05
Depth=    3260 States= 1.28e+08 Transitions= 3.35e+08 Memory=  6964.139 t= 1.11e+03 R=   1e+05
Depth=    3260 States= 1.29e+08 Transitions= 3.39e+08 Memory=  7029.942 t= 1.12e+03 R=   1e+05
Depth=    3260 States=  1.3e+08 Transitions= 3.43e+08 Memory=  7096.223 t= 1.14e+03 R=   1e+05
Depth=    3260 States= 1.31e+08 Transitions= 3.47e+08 Memory=  7161.073 t= 1.15e+03 R=   1e+05
Depth=    3260 States= 1.32e+08 Transitions= 3.51e+08 Memory=  7224.492 t= 1.16e+03 R=   1e+05
Depth=    3260 States= 1.33e+08 Transitions= 3.54e+08 Memory=  7273.129 t= 1.17e+03 R=   1e+05
Depth=    3260 States= 1.34e+08 Transitions= 3.56e+08 Memory=  7310.799 t= 1.18e+03 R=   1e+05
Depth=    3260 States= 1.35e+08 Transitions= 3.59e+08 Memory=  7345.609 t= 1.19e+03 R=   1e+05
pan: resizing hashtable to -w28..  done
Depth=    3260 States= 1.36e+08 Transitions= 3.61e+08 Memory=  9393.609 t= 1.22e+03 R=   1e+05
Depth=    3260 States= 1.37e+08 Transitions= 3.63e+08 Memory=  9401.238 t= 1.22e+03 R=   1e+05
Depth=    3260 States= 1.38e+08 Transitions= 3.66e+08 Memory=  9437.001 t= 1.23e+03 R=   1e+05
Depth=    3346 States= 1.39e+08 Transitions= 3.68e+08 Memory=  9472.764 t= 1.24e+03 R=   1e+05
Depth=    3346 States=  1.4e+08 Transitions=  3.7e+08 Memory=  9507.573 t= 1.25e+03 R=   1e+05
Depth=    3346 States= 1.41e+08 Transitions= 3.73e+08 Memory=  9543.335 t= 1.25e+03 R=   1e+05
Depth=    3346 States= 1.42e+08 Transitions= 3.75e+08 Memory=  9578.621 t= 1.26e+03 R=   1e+05
Depth=    3346 States= 1.43e+08 Transitions= 3.78e+08 Memory=  9616.768 t= 1.27e+03 R=   1e+05
Depth=    3346 States= 1.44e+08 Transitions=  3.8e+08 Memory=  9652.054 t= 1.28e+03 R=   1e+05
Depth=    3346 States= 1.45e+08 Transitions= 3.82e+08 Memory=  9687.340 t= 1.29e+03 R=   1e+05
Depth=    3346 States= 1.46e+08 Transitions= 3.85e+08 Memory=  9721.673 t= 1.29e+03 R=   1e+05
Depth=    3346 States= 1.47e+08 Transitions= 3.87e+08 Memory=  9756.482 t=  1.3e+03 R=   1e+05
Depth=    3346 States= 1.48e+08 Transitions= 3.89e+08 Memory=  9790.814 t= 1.31e+03 R=   1e+05
Depth=    3346 States= 1.49e+08 Transitions= 3.92e+08 Memory=  9853.280 t= 1.32e+03 R=   1e+05
Depth=    3346 States=  1.5e+08 Transitions= 3.94e+08 Memory=  9923.851 t= 1.32e+03 R=   1e+05
Depth=    3346 States= 1.51e+08 Transitions= 3.97e+08 Memory=  9993.470 t= 1.33e+03 R=   1e+05
Depth=    3346 States= 1.52e+08 Transitions= 3.99e+08 Memory= 10062.134 t= 1.34e+03 R=   1e+05
Depth=    3346 States= 1.53e+08 Transitions= 4.02e+08 Memory= 10131.276 t= 1.35e+03 R=   1e+05
Depth=    3346 States= 1.54e+08 Transitions= 4.05e+08 Memory= 10199.940 t= 1.36e+03 R=   1e+05
Depth=    3346 States= 1.55e+08 Transitions= 4.07e+08 Memory= 10269.082 t= 1.37e+03 R=   1e+05
Depth=    3346 States= 1.56e+08 Transitions=  4.1e+08 Memory= 10338.223 t= 1.38e+03 R=   1e+05
Depth=    3346 States= 1.57e+08 Transitions= 4.12e+08 Memory= 10407.364 t= 1.39e+03 R=   1e+05
Depth=    3438 States= 1.58e+08 Transitions= 4.15e+08 Memory= 10476.506 t= 1.39e+03 R=   1e+05
Depth=    3438 States= 1.59e+08 Transitions= 4.17e+08 Memory= 10545.647 t=  1.4e+03 R=   1e+05
Depth=    3438 States=  1.6e+08 Transitions=  4.2e+08 Memory= 10614.312 t= 1.41e+03 R=   1e+05
Depth=    3438 States= 1.61e+08 Transitions= 4.22e+08 Memory= 10682.976 t= 1.42e+03 R=   1e+05
Depth=    3438 States= 1.62e+08 Transitions= 4.25e+08 Memory= 10751.641 t= 1.43e+03 R=   1e+05
Depth=    3438 States= 1.63e+08 Transitions= 4.27e+08 Memory= 10820.782 t= 1.44e+03 R=   1e+05
Depth=    3438 States= 1.64e+08 Transitions=  4.3e+08 Memory= 10889.447 t= 1.45e+03 R=   1e+05
Depth=    3438 States= 1.65e+08 Transitions= 4.33e+08 Memory= 10959.065 t= 1.46e+03 R=   1e+05
Depth=    3438 States= 1.66e+08 Transitions= 4.35e+08 Memory= 11028.206 t= 1.46e+03 R=   1e+05
Depth=    3438 States= 1.67e+08 Transitions= 4.38e+08 Memory= 11096.871 t= 1.47e+03 R=   1e+05
Depth=    3438 States= 1.68e+08 Transitions=  4.4e+08 Memory= 11166.012 t= 1.48e+03 R=   1e+05
Depth=    3438 States= 1.69e+08 Transitions= 4.43e+08 Memory= 11226.094 t= 1.49e+03 R=   1e+05
Depth=    3438 States=  1.7e+08 Transitions= 4.45e+08 Memory= 11288.559 t=  1.5e+03 R=   1e+05
Depth=    3438 States= 1.71e+08 Transitions= 4.47e+08 Memory= 11357.224 t= 1.51e+03 R=   1e+05
Depth=    3438 States= 1.72e+08 Transitions=  4.5e+08 Memory= 11425.889 t= 1.52e+03 R=   1e+05
Depth=    3438 States= 1.73e+08 Transitions= 4.53e+08 Memory= 11494.553 t= 1.52e+03 R=   1e+05
Depth=    3438 States= 1.74e+08 Transitions= 4.56e+08 Memory= 11563.694 t= 1.53e+03 R=   1e+05
Depth=    3438 States= 1.75e+08 Transitions= 4.58e+08 Memory= 11630.452 t= 1.54e+03 R=   1e+05
Depth=    3438 States= 1.76e+08 Transitions= 4.61e+08 Memory= 11668.122 t= 1.55e+03 R=   1e+05
Depth=    3438 States= 1.77e+08 Transitions= 4.63e+08 Memory= 11704.838 t= 1.56e+03 R=   1e+05
Depth=    3438 States= 1.78e+08 Transitions= 4.66e+08 Memory= 11740.124 t= 1.57e+03 R=   1e+05
Depth=    3438 States= 1.79e+08 Transitions= 4.68e+08 Memory= 11774.933 t= 1.57e+03 R=   1e+05
Depth=    3438 States=  1.8e+08 Transitions=  4.7e+08 Memory= 11811.173 t= 1.58e+03 R=   1e+05
Depth=    3438 States= 1.81e+08 Transitions= 4.73e+08 Memory= 11847.413 t= 1.59e+03 R=   1e+05
Depth=    3438 States= 1.82e+08 Transitions= 4.75e+08 Memory= 11881.745 t=  1.6e+03 R=   1e+05
Depth=    3438 States= 1.83e+08 Transitions= 4.78e+08 Memory= 11916.554 t=  1.6e+03 R=   1e+05
Depth=    3438 States= 1.84e+08 Transitions=  4.8e+08 Memory= 11951.363 t= 1.61e+03 R=   1e+05
Depth=    3438 States= 1.85e+08 Transitions= 4.83e+08 Memory= 11987.126 t= 1.62e+03 R=   1e+05
Depth=    3438 States= 1.86e+08 Transitions= 4.85e+08 Memory= 12021.458 t= 1.63e+03 R=   1e+05
Depth=    3438 States= 1.87e+08 Transitions= 4.87e+08 Memory= 12060.082 t= 1.64e+03 R=   1e+05
Depth=    3438 States= 1.88e+08 Transitions=  4.9e+08 Memory= 12095.368 t= 1.64e+03 R=   1e+05
Depth=    3438 States= 1.89e+08 Transitions= 4.92e+08 Memory= 12130.177 t= 1.65e+03 R=   1e+05
Depth=    3438 States=  1.9e+08 Transitions= 4.95e+08 Memory= 12165.463 t= 1.66e+03 R=   1e+05
Depth=    3438 States= 1.91e+08 Transitions= 4.97e+08 Memory= 12199.795 t= 1.67e+03 R=   1e+05
Depth=    3438 States= 1.92e+08 Transitions=    5e+08 Memory= 12234.128 t= 1.68e+03 R=   1e+05
Depth=    3438 States= 1.93e+08 Transitions= 5.02e+08 Memory= 12268.460 t= 1.68e+03 R=   1e+05
Depth=    3438 States= 1.94e+08 Transitions= 5.06e+08 Memory= 12336.171 t=  1.7e+03 R=   1e+05
Depth=    3438 States= 1.95e+08 Transitions=  5.1e+08 Memory= 12404.835 t= 1.71e+03 R=   1e+05
Depth=    3438 States= 1.96e+08 Transitions= 5.14e+08 Memory= 12473.500 t= 1.72e+03 R=   1e+05
Depth=    3438 States= 1.97e+08 Transitions= 5.18e+08 Memory= 12542.164 t= 1.74e+03 R=   1e+05
Depth=    3438 States= 1.98e+08 Transitions= 5.22e+08 Memory= 12610.829 t= 1.75e+03 R=   1e+05
Depth=    3438 States= 1.99e+08 Transitions= 5.26e+08 Memory= 12679.493 t= 1.76e+03 R=   1e+05
Depth=    3438 States=    2e+08 Transitions=  5.3e+08 Memory= 12748.158 t= 1.78e+03 R=   1e+05
Depth=    3438 States= 2.01e+08 Transitions= 5.34e+08 Memory= 12817.299 t= 1.79e+03 R=   1e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (eventually_prerequisites)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1644 byte, depth reached 3438, errors: 0
1.518078e+08 states, stored (2.01894e+08 visited)
3.3543075e+08 states, matched
5.3732503e+08 transitions (= visited+matched)
8.7199076e+08 atomic steps
hash conflicts: 1.357451e+08 (resolved)

Stats on memory usage (in Megabytes):
243222.341      equivalent memory usage for states (stored*(State-vector + overhead))
10827.437       actual memory usage for states (compression: 4.45%)
                state-vector as stored = 39 byte + 36 byte overhead
 2048.000       memory used for hash table (-w28)
    3.662       memory used for DFS stack (-m60000)
12878.335       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:705292 2:12 3:1603 4:62536 5:80 6:2 ]

pan: elapsed time 1.8e+03 seconds
pan: rate 111953.89 states/second
```

`ltl ensure_priority`

```
$ make run
spin -a preemptive.pml
ltl ensure_priority: [] ((! (((((((((((((((waking[0]==0)) && ((waking[1]==0))) && ((waking[2]==0))) && ((waking[3]==0))) && ((len(ipi_requests[0])==0))) && ((len(ipi_requests[1])==0))) && (! (handling_interrupt[0]))) && (! (handling_interrupt[1]))) && (! (handling_interrupt[2]))) && (! (handling_interrupt[3]))) && ((RUNNING[0]!=-(1)))) && ((RUNNING[1]!=-(1)))) && ((RUNNING[0]!=runnable_preempted_highest_priority))) && ((RUNNING[1]!=runnable_preempted_highest_priority)))) || ((running_lowest_priority<runnable_preempted_highest_priority)))
gcc -O3 -DCOLLAPSE -DVECTORSZ=5000 -DNFAIR=3 -o pan pan.c
rm -f *.trail
./pan -a -n -m60000
Depth=    2764 States=    1e+06 Transitions= 1.96e+06 Memory=   200.327 t=     5.65 R=   2e+05
Depth=    2764 States=    2e+06 Transitions= 3.91e+06 Memory=   265.177 t=     11.1 R=   2e+05
Depth=    2764 States=    3e+06 Transitions= 5.89e+06 Memory=   331.934 t=     16.6 R=   2e+05
Depth=    2764 States=    4e+06 Transitions= 7.85e+06 Memory=   393.446 t=     22.1 R=   2e+05
Depth=    2764 States=    5e+06 Transitions= 9.81e+06 Memory=   459.249 t=     27.6 R=   2e+05
Depth=    3053 States=    6e+06 Transitions= 1.18e+07 Memory=   523.622 t=     33.2 R=   2e+05
Depth=    3053 States=    7e+06 Transitions= 1.37e+07 Memory=   587.519 t=     38.8 R=   2e+05
Depth=    3053 States=    8e+06 Transitions= 1.57e+07 Memory=   649.984 t=     44.4 R=   2e+05
Depth=    3248 States=    9e+06 Transitions= 1.77e+07 Memory=   713.404 t=       50 R=   2e+05
Depth=    3257 States=    1e+07 Transitions= 1.96e+07 Memory=   789.221 t=     55.7 R=   2e+05
Depth=    3257 States=  1.1e+07 Transitions= 2.16e+07 Memory=   859.316 t=     61.4 R=   2e+05
Depth=    3257 States=  1.2e+07 Transitions= 2.35e+07 Memory=   927.980 t=     67.1 R=   2e+05
Depth=    3257 States=  1.3e+07 Transitions= 2.55e+07 Memory=   996.645 t=     72.9 R=   2e+05
Depth=    3257 States=  1.4e+07 Transitions= 2.74e+07 Memory=  1065.309 t=     78.6 R=   2e+05
Depth=    3260 States=  1.5e+07 Transitions= 2.94e+07 Memory=  1134.451 t=     84.3 R=   2e+05
Depth=    3260 States=  1.6e+07 Transitions= 3.14e+07 Memory=  1204.069 t=     90.1 R=   2e+05
Depth=    3260 States=  1.7e+07 Transitions= 3.33e+07 Memory=  1272.257 t=     95.9 R=   2e+05
Depth=    3260 States=  1.8e+07 Transitions= 3.53e+07 Memory=  1342.352 t=      102 R=   2e+05
Depth=    3260 States=  1.9e+07 Transitions= 3.72e+07 Memory=  1411.016 t=      108 R=   2e+05
Depth=    3260 States=    2e+07 Transitions= 3.92e+07 Memory=  1479.204 t=      114 R=   2e+05
Depth=    3260 States=  2.1e+07 Transitions= 4.11e+07 Memory=  1547.392 t=      119 R=   2e+05
Depth=    3260 States=  2.2e+07 Transitions= 4.31e+07 Memory=  1615.580 t=      125 R=   2e+05
Depth=    3260 States=  2.3e+07 Transitions= 4.51e+07 Memory=  1684.721 t=      131 R=   2e+05
Depth=    3260 States=  2.4e+07 Transitions=  4.7e+07 Memory=  1751.478 t=      137 R=   2e+05
Depth=    3260 States=  2.5e+07 Transitions=  4.9e+07 Memory=  1812.513 t=      143 R=   2e+05
Depth=    3260 States=  2.6e+07 Transitions=  5.1e+07 Memory=  1875.456 t=      149 R=   2e+05
Depth=    3260 States=  2.7e+07 Transitions= 5.29e+07 Memory=  1936.968 t=      154 R=   2e+05
Depth=    3260 States=  2.8e+07 Transitions= 5.49e+07 Memory=  1999.910 t=      160 R=   2e+05
Depth=    3260 States=  2.9e+07 Transitions= 5.69e+07 Memory=  2061.422 t=      166 R=   2e+05
Depth=    3260 States=    3e+07 Transitions= 5.88e+07 Memory=  2125.795 t=      172 R=   2e+05
Depth=    3260 States=  3.1e+07 Transitions= 6.08e+07 Memory=  2193.983 t=      178 R=   2e+05
Depth=    3260 States=  3.2e+07 Transitions= 6.27e+07 Memory=  2262.171 t=      184 R=   2e+05
Depth=    3260 States=  3.3e+07 Transitions= 6.47e+07 Memory=  2330.358 t=      190 R=   2e+05
Depth=    3260 States=  3.4e+07 Transitions= 6.66e+07 Memory=  2399.023 t=      196 R=   2e+05
pan: resizing hashtable to -w26..  done
Depth=    3260 States=  3.5e+07 Transitions= 6.86e+07 Memory=  2963.475 t=      207 R=   2e+05
Depth=    3260 States=  3.6e+07 Transitions= 7.06e+07 Memory=  3032.140 t=      212 R=   2e+05
Depth=    3260 States=  3.7e+07 Transitions= 7.25e+07 Memory=  3100.327 t=      218 R=   2e+05
Depth=    3260 States=  3.8e+07 Transitions= 7.45e+07 Memory=  3168.515 t=      224 R=   2e+05
Depth=    3260 States=  3.9e+07 Transitions= 7.64e+07 Memory=  3236.226 t=      230 R=   2e+05
Depth=    3260 States=    4e+07 Transitions= 7.84e+07 Memory=  3305.844 t=      235 R=   2e+05
Depth=    3260 States=  4.1e+07 Transitions= 8.03e+07 Memory=  3377.847 t=      241 R=   2e+05
Depth=    3260 States=  4.2e+07 Transitions= 8.23e+07 Memory=  3448.418 t=      247 R=   2e+05
Depth=    3260 States=  4.3e+07 Transitions= 8.43e+07 Memory=  3517.083 t=      253 R=   2e+05
Depth=    3260 States=  4.4e+07 Transitions= 8.62e+07 Memory=  3586.701 t=      258 R=   2e+05
Depth=    3260 States=  4.5e+07 Transitions= 8.82e+07 Memory=  3648.690 t=      264 R=   2e+05
Depth=    3260 States=  4.6e+07 Transitions= 9.02e+07 Memory=  3712.586 t=      270 R=   2e+05
Depth=    3260 States=  4.7e+07 Transitions= 9.21e+07 Memory=  3777.913 t=      276 R=   2e+05
Depth=    3260 States=  4.8e+07 Transitions= 9.41e+07 Memory=  3841.332 t=      281 R=   2e+05
Depth=    3260 States=  4.9e+07 Transitions=  9.6e+07 Memory=  3904.752 t=      287 R=   2e+05
Depth=    3260 States=    5e+07 Transitions=  9.8e+07 Memory=  3972.462 t=      293 R=   2e+05
Depth=    3260 States=  5.1e+07 Transitions=    1e+08 Memory=  4037.789 t=      298 R=   2e+05
Depth=    3260 States=  5.2e+07 Transitions= 1.02e+08 Memory=  4102.162 t=      304 R=   2e+05
Depth=    3260 States=  5.3e+07 Transitions= 1.04e+08 Memory=  4173.688 t=      310 R=   2e+05
Depth=    3260 States=  5.4e+07 Transitions= 1.06e+08 Memory=  4241.875 t=      316 R=   2e+05
Depth=    3260 States=  5.5e+07 Transitions= 1.08e+08 Memory=  4311.017 t=      322 R=   2e+05
Depth=    3260 States=  5.6e+07 Transitions=  1.1e+08 Memory=  4379.681 t=      328 R=   2e+05
Depth=    3260 States=  5.7e+07 Transitions= 1.12e+08 Memory=  4446.915 t=      334 R=   2e+05
Depth=    3260 States=  5.8e+07 Transitions= 1.14e+08 Memory=  4514.150 t=      340 R=   2e+05
Depth=    3260 States=  5.9e+07 Transitions= 1.16e+08 Memory=  4575.185 t=      346 R=   2e+05
Depth=    3260 States=    6e+07 Transitions= 1.18e+08 Memory=  4638.604 t=      351 R=   2e+05
Depth=    3260 States=  6.1e+07 Transitions=  1.2e+08 Memory=  4706.315 t=      357 R=   2e+05
Depth=    3260 States=  6.2e+07 Transitions= 1.22e+08 Memory=  4774.503 t=      363 R=   2e+05
Depth=    3260 States=  6.3e+07 Transitions= 1.24e+08 Memory=  4842.213 t=      369 R=   2e+05
Depth=    3260 States=  6.4e+07 Transitions= 1.26e+08 Memory=  4913.739 t=      375 R=   2e+05
Depth=    3260 States=  6.5e+07 Transitions= 1.28e+08 Memory=  4981.450 t=      381 R=   2e+05
Depth=    3260 States=  6.6e+07 Transitions=  1.3e+08 Memory=  5043.916 t=      387 R=   2e+05
Depth=    3260 States=  6.7e+07 Transitions= 1.32e+08 Memory=  5112.103 t=      393 R=   2e+05
Depth=    3260 States=  6.8e+07 Transitions= 1.34e+08 Memory=  5186.013 t=      399 R=   2e+05
Depth=    3260 States=  6.9e+07 Transitions= 1.36e+08 Memory=  5257.539 t=      405 R=   2e+05
Depth=    3260 States=    7e+07 Transitions= 1.38e+08 Memory=  5328.111 t=      411 R=   2e+05
Depth=    3260 States=  7.1e+07 Transitions=  1.4e+08 Memory=  5397.729 t=      417 R=   2e+05
Depth=    3260 States=  7.2e+07 Transitions= 1.42e+08 Memory=  5466.870 t=      423 R=   2e+05
Depth=    3260 States=  7.3e+07 Transitions= 1.43e+08 Memory=  5535.535 t=      429 R=   2e+05
Depth=    3260 States=  7.4e+07 Transitions= 1.45e+08 Memory=  5606.107 t=      435 R=   2e+05
Depth=    3260 States=  7.5e+07 Transitions= 1.47e+08 Memory=  5676.678 t=      441 R=   2e+05
Depth=    3260 States=  7.6e+07 Transitions= 1.49e+08 Memory=  5747.727 t=      447 R=   2e+05
Depth=    3438 States=  7.7e+07 Transitions= 1.51e+08 Memory=  5817.345 t=      453 R=   2e+05
Depth=    3438 States=  7.8e+07 Transitions= 1.53e+08 Memory=  5886.487 t=      459 R=   2e+05
Depth=    3438 States=  7.9e+07 Transitions= 1.55e+08 Memory=  5955.151 t=      465 R=   2e+05
Depth=    3438 States=    8e+07 Transitions= 1.57e+08 Memory=  6024.770 t=      471 R=   2e+05
Depth=    3438 States=  8.1e+07 Transitions= 1.59e+08 Memory=  6094.865 t=      477 R=   2e+05
Depth=    3438 States=  8.2e+07 Transitions= 1.61e+08 Memory=  6164.006 t=      483 R=   2e+05
Depth=    3438 States=  8.3e+07 Transitions= 1.63e+08 Memory=  6234.101 t=      489 R=   2e+05
Depth=    3438 States=  8.4e+07 Transitions= 1.65e+08 Memory=  6307.534 t=      495 R=   2e+05
Depth=    3438 States=  8.5e+07 Transitions= 1.67e+08 Memory=  6376.675 t=      501 R=   2e+05
Depth=    3438 States=  8.6e+07 Transitions= 1.69e+08 Memory=  6445.340 t=      507 R=   2e+05
Depth=    3438 States=  8.7e+07 Transitions= 1.71e+08 Memory=  6515.435 t=      513 R=   2e+05
Depth=    3438 States=  8.8e+07 Transitions= 1.73e+08 Memory=  6585.053 t=      519 R=   2e+05
Depth=    3438 States=  8.9e+07 Transitions= 1.75e+08 Memory=  6653.718 t=      525 R=   2e+05
Depth=    3438 States=    9e+07 Transitions= 1.77e+08 Memory=  6722.859 t=      531 R=   2e+05
Depth=    3438 States=  9.1e+07 Transitions= 1.79e+08 Memory=  6791.524 t=      537 R=   2e+05
Depth=    3438 States=  9.2e+07 Transitions= 1.81e+08 Memory=  6860.188 t=      543 R=   2e+05
Depth=    3438 States=  9.3e+07 Transitions= 1.83e+08 Memory=  6930.760 t=      549 R=   2e+05
Depth=    3438 States=  9.4e+07 Transitions= 1.85e+08 Memory=  7003.716 t=      555 R=   2e+05
Depth=    3438 States=  9.5e+07 Transitions= 1.87e+08 Memory=  7074.288 t=      562 R=   2e+05
Depth=    3438 States=  9.6e+07 Transitions= 1.89e+08 Memory=  7146.291 t=      568 R=   2e+05
Depth=    3438 States=  9.7e+07 Transitions= 1.91e+08 Memory=  7215.909 t=      574 R=   2e+05
Depth=    3438 States=  9.8e+07 Transitions= 1.93e+08 Memory=  7285.527 t=      580 R=   2e+05
Depth=    3438 States=  9.9e+07 Transitions= 1.95e+08 Memory=  7359.437 t=      586 R=   2e+05
Depth=    3438 States=    1e+08 Transitions= 1.97e+08 Memory=  7430.009 t=      593 R=   2e+05
Depth=    3438 States= 1.01e+08 Transitions= 1.99e+08 Memory=  7498.673 t=      599 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction
        + Compression

Full statespace search for:
        never claim             + (ensure_priority)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 1644 byte, depth reached 3438, errors: 0
1.0172133e+08 states, stored
 98261497 states, matched
1.9998282e+08 transitions (= stored+matched)
3.4339604e+08 atomic steps
hash conflicts:  69991370 (resolved)

Stats on memory usage (in Megabytes):
162975.149      equivalent memory usage for states (stored*(State-vector + overhead))
 7033.508       actual memory usage for states (compression: 4.32%)
                state-vector as stored = 37 byte + 36 byte overhead
  512.000       memory used for hash table (-w26)
    3.662       memory used for DFS stack (-m60000)
 7548.264       total actual memory usage


nr of templates: [ 0:globals 1:chans 2:procs ]
collapse counts: [ 0:705292 2:12 3:1603 4:62536 5:80 6:1 ]

pan: elapsed time 603 seconds
pan: rate 168555.12 states/second
```
