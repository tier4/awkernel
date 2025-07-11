make clean
make TARGET=CONCURRENT_WORK_CONSERVATION TIMER=TIMER_EDGE run | tee concurrent_work_conservation_edge.out

make clean
make TARGET=CPU_WAKING_TO_ACTIVE_CPU0 TIMER=TIMER_EDGE run | tee cpu_waking_to_active_cpu0_edge.out

make clean
make TARGET=CPU_WAKING_TO_ACTIVE_CPU1 TIMER=TIMER_EDGE run | tee cpu_waking_to_active_cpu1_edge.out

make clean
make TARGET=EVENTUALLY_EXECUTE TIMER=TIMER_EDGE run | tee eventually_execute_edge.out


make clean
make TARGET=CONCURRENT_WORK_CONSERVATION TIMER=TIMER_LEVEL run | tee concurrent_work_conservation_level.out

make clean
make TARGET=CPU_WAKING_TO_ACTIVE_CPU0 TIMER=TIMER_LEVEL run | tee cpu_waking_to_active_cpu0_level.out

make clean
make TARGET=CPU_WAKING_TO_ACTIVE_CPU1 TIMER=TIMER_LEVEL run | tee cpu_waking_to_active_cpu1_level.out

make clean
make TARGET=EVENTUALLY_EXECUTE TIMER=TIMER_LEVEL run | tee eventually_execute_level.out
