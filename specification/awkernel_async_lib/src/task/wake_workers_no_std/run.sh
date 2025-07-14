for i in $(seq 0 3); do
    echo "IRQ_POS$i"

    # Edge-triggered timer
    make clean
    make IRQ_POS=$i TARGET=CONCURRENT_WORK_CONSERVATION TIMER=TIMER_EDGE run | tee concurrent_work_conservation_edge_irq$i.out

    if [ -e "wake_workers.pml.trail" ]; then
        echo "wake_workers.pml.trail ファイルが存在します。終了します。"
        exit 1
    fi

    make clean
    make IRQ_POS=$i TARGET=CPU_WAKING_TO_ACTIVE_CPU0 TIMER=TIMER_EDGE run | tee cpu_waking_to_active_cpu0_edge_irq$i.out

    if [ -e "wake_workers.pml.trail" ]; then
        echo "wake_workers.pml.trail ファイルが存在します。終了します。"
        exit 1
    fi

    make clean
    make IRQ_POS=$i TARGET=CPU_WAKING_TO_ACTIVE_CPU1 TIMER=TIMER_EDGE run | tee cpu_waking_to_active_cpu1_edge_irq$i.out

    if [ -e "wake_workers.pml.trail" ]; then
        echo "wake_workers.pml.trail ファイルが存在します。終了します。"
        exit 1
    fi

    make clean
    make IRQ_POS=$i TARGET=EVENTUALLY_EXECUTE TIMER=TIMER_EDGE run | tee eventually_execute_edge_irq$i.out

    if [ -e "wake_workers.pml.trail" ]; then
        echo "wake_workers.pml.trail ファイルが存在します。終了します。"
        exit 1
    fi

    # Level-triggered timer
    make clean
    make IRQ_POS=$i TARGET=CONCURRENT_WORK_CONSERVATION TIMER=TIMER_LEVEL run | tee concurrent_work_conservation_level_irq$i.out

    if [ -e "wake_workers.pml.trail" ]; then
        echo "wake_workers.pml.trail ファイルが存在します。終了します。"
        exit 1
    fi

    make clean
    make IRQ_POS=$i TARGET=CPU_WAKING_TO_ACTIVE_CPU0 TIMER=TIMER_LEVEL run | tee cpu_waking_to_active_cpu0_level_irq$i.out

    if [ -e "wake_workers.pml.trail" ]; then
        echo "wake_workers.pml.trail ファイルが存在します。終了します。"
        exit 1
    fi

    make clean
    make IRQ_POS=$i TARGET=CPU_WAKING_TO_ACTIVE_CPU1 TIMER=TIMER_LEVEL run | tee cpu_waking_to_active_cpu1_level_irq$i.out

    if [ -e "wake_workers.pml.trail" ]; then
        echo "wake_workers.pml.trail ファイルが存在します。終了します。"
        exit 1
    fi

    make clean
    make IRQ_POS=$i TARGET=EVENTUALLY_EXECUTE TIMER=TIMER_LEVEL run | tee eventually_execute_level_irq$i.out

    if [ -e "wake_workers.pml.trail" ]; then
        echo "wake_workers.pml.trail ファイルが存在します。終了します。"
        exit 1
    fi
done