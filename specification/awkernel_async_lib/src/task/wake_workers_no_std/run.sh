make clean
make TARGET=CPU_WAKING_TO_ACTIVE run | tee cpu_waking_to_active.out

make clean
make TARGET=EVENTUALLY_EXECUTE run | tee eventually_execute.out