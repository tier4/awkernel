make clean
make TARGET=CPU_WAKING_TO_ACTIVE TIMER=TIMER_EDGE run | tee cpu_waking_to_active_edge.out

make clean
make TARGET=EVENTUALLY_EXECUTE TIMER=TIMER_EDGE run | tee eventually_execute_edge.out

make clean
make TARGET=CPU_WAKING_TO_ACTIVE TIMER=TIMER_LEVEL run | tee cpu_waking_to_active_level.out

make clean
make TARGET=EVENTUALLY_EXECUTE TIMER=TIMER_LEVEL run | tee eventually_execute_level.out
