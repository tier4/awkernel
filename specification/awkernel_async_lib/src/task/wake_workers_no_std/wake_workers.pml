#define WORKERS 3
#define TASK_NUM (WORKERS + 1)
#define CPU_NUM (WORKERS + 1)

mtype = { Idle, Waiting, Waking };
mtype CPU_SLEEP_TAG[CPU_NUM];

byte interrupt_mask[CPU_NUM];
byte IPI[CPU_NUM];             // edge-trigger interrupt
byte timer_enable[CPU_NUM];
byte timer_interrupt[CPU_NUM]; // level-sensitive interrupt

byte run_queue = 1;
byte num_blocking = 0;
byte created_task = 1;

byte int_pos;

inline compare_exchange(target, current, new, prev)
{
    d_step {
        prev = target;
        if
        :: target == current ->
            target = new;
        :: else
        fi
    }
}

inline send_ipi(cpu_id) {
    d_step {
        printf("send IPI to CPU#{%d}, interrupt_mask[%d] = %d\n", cpu_id, cpu_id, interrupt_mask[cpu_id]);
        if
        :: interrupt_mask[cpu_id] == 0 -> IPI[cpu_id] = 1;
        :: else
        fi
    }
}

inline interrupt_handler(cpu_id) {
    // disable interrupts
    atomic {
        if
        :: interrupt_mask[cpu_id] == 0 -> interrupt_mask[cpu_id] = 1;
        :: else -> goto return_interrupt_handler;
        fi

        // handle IPI
        if
        :: d_step { IPI[cpu_id] == 1 ->
            IPI[cpu_id] = 0;
            printf("CPU#{%d}: handle IPI\n", cpu_id);
        }
        :: else
        fi

        // handle timer interrupt
        if
        :: timer_enable[cpu_id] == 1 && timer_interrupt[cpu_id] == 1 ->
            timer_interrupt[cpu_id] = 0;
            printf("CPU#{%d}: handle timer interrupt\n", cpu_id);
        :: else
        fi

        // Enable timer.
        // `handle_irqs() and `handle_irq()` in awkernel_lib/src/interrupt.rs.
        // `reset_wakeup_timer()` in awkernel_lib/src/cpu/sleep_cpu_no_std.rs.
        if
        :: CPU_SLEEP_TAG[cpu_id] == Waiting -> timer_reset(cpu_id)
        :: else
        fi
    }

    // enable interrupts
    interrupt_mask[cpu_id] = 1;
return_interrupt_handler:
}

inline wait_interrupt(cpu_id) {
    if
    :: (timer_enable[cpu_id] == 1 && timer_interrupt[cpu_id] == 1)
    :: IPI[cpu_id]
    fi
}

inline rnd5() {
    if
    :: true -> rnd = 0
    :: true -> rnd = 1
    :: true -> rnd = 2
    :: true -> rnd = 3
    :: true -> rnd = 4
    fi
}

// `SleepCpuNoStd::sleep()` in awkernel_lib/src/cpu/sleep_cpu_no_std.rs
inline sleep(cpu_id) {
    // if wake-up already pending, consume and return
    if
    :: CPU_SLEEP_TAG[cpu_id] == Waking -> goto return_sleep2;
    :: else
    fi

    byte rnd; // chose the position interrupts occur
    d_step {
        // enable interrupts and halt until IPI arrives
        interrupt_mask[cpu_id] = 0;
        rnd5();
    }

    // receive interrupts
    if
    :: rnd == 0 -> interrupt_handler(cpu_id)
    :: else
    fi

    // mark waiting before halt
    mtype prev_val;
    compare_exchange(CPU_SLEEP_TAG[cpu_id], Idle, Waiting, prev_val);

    if
    :: prev_val == Idle
    :: prev_val == Waking -> goto return_sleep1;
    :: else -> assert(prev_val != Waiting); // unreachable!()
    fi

    // receive interrupts
    if
    :: rnd == 1 -> interrupt_handler(cpu_id)
    :: else
    fi

    // In case that there are any tasks to run,
    // wake up the primary CPU to wake me up.
    byte tmp;
    wake_up(cpu_id, 0, tmp);

    // receive interrupts
    if
    :: rnd == 2 -> interrupt_handler(cpu_id)
    :: else
    fi

    if
    :: atomic { CPU_SLEEP_TAG[cpu_id] == Waking ->
        CPU_SLEEP_TAG[cpu_id] = Idle;
        goto return_sleep1;
    }
    :: else
    fi

    // Rare Case:
    //   IPIs sent during interrupt handlers invoked here will be ignored because IPIs are edge-trigger.
    //   To notify it again, Awkernel setup a timer by `reset_wakeup_timer()` in interrupt handlers.

    // receive interrupts
    if
    :: rnd == 3 -> interrupt_handler(cpu_id)
    :: else
    fi

    wait_interrupt(cpu_id);

    interrupt_handler(cpu_id);

return_sleep1:
    // disable interrupts
    interrupt_mask[cpu_id] = 1;

return_sleep2:
    CPU_SLEEP_TAG[cpu_id] = Idle;
}

// `SleepCpuNoStd::wake_up()` in awkernel_lib/src/cpu/sleep_cpu_no_std.rs
inline wake_up(my_id, target_cpu_id, result) {
    if
    :: atomic { my_id == target_cpu_id ->
        result = 0;
        goto return_wake_up;
    }
    :: else
    fi

    mtype tag;
    mtype prev;

    // attempt state transitions until success or redundant
    if
    :: atomic { CPU_SLEEP_TAG[target_cpu_id] == Idle ->
        // CPU not yet sleeping: schedule wake-up
        CPU_SLEEP_TAG[target_cpu_id] = Waking;
        result = 1;
        printf("Idle -> Waking: CPU#{%d}", target_cpu_id);
        goto return_wake_up;
    }
    :: atomic { CPU_SLEEP_TAG[target_cpu_id] == Waiting ->
         // CPU is halted: send IPI
        CPU_SLEEP_TAG[target_cpu_id] = Waking;
        result = 1;
        printf("Waiting -> Waking: CPU#{%d}", target_cpu_id);
    }
        send_ipi(target_cpu_id);
        goto return_wake_up;
    :: atomic { CPU_SLEEP_TAG[target_cpu_id] == Waking ->
        // wake-up already pending
        printf("already waking: CPU#{%d}", target_cpu_id);
        result = 0;
    }
        send_ipi(target_cpu_id);
        goto return_wake_up;
    fi

return_wake_up:
}

// `wake_workers()` in awkernel_async_lib/src/task.rs
inline wake_workers(cpu_id) {
    byte num_tasks = run_queue;
    byte i;
    byte result;

    for (i: 1 .. CPU_NUM - 1) {
        if
        :: num_tasks == 0 -> break;
        :: else ->
            wake_up(cpu_id, i, result);

            if
            :: d_step { result == 1 ->
                printf("wake_up(%d)\n", i);
                num_tasks--;
            }
            :: else
            fi
        fi
    }
}

inline timer_reset(cpu_id) {
    printf("CPU#{%d}: reset timer\n", cpu_id);
    timer_enable[cpu_id] = 1;
}

inline timer_disable(cpu_id) {
    d_step {
        printf("CPU#{%d}: disable timer\n", cpu_id);
        timer_enable[cpu_id] = 2;
    }
}

// Simulate tasks
inline task_poll() {
    byte result;

    // spawn a new task
    // `Task::wake()` in awkernel_async_lib/src/task.rs
    if
    :: atomic { created_task < TASK_NUM ->
        created_task++;
        run_queue++;
    }
        wake_up(CPU_NUM, 0, result);
    :: else
    fi

    if
    :: true ->
        if
        // Simulate blocking tasks.
        // Even if there are `WORKERS - 1` blocking tasks,
        // every task will be woken up.
        :: d_step { num_blocking < WORKERS - 1 ->
            num_blocking++;
            printf("num_blocking = %d, cpu_id = %d\n", num_blocking, cpu_id);
        }
        :: else
        fi
    :: true
    fi
}

// `run_main()` in awkernel_async_lib/src/task.rs
proctype run_main(byte cpu_id) {
    do
    :: d_step { run_queue > 0 ->
        run_queue--;
        printf("run_queue--: run_queue = %d\n", run_queue);
    };
        task_poll();
    :: else ->
        sleep(cpu_id);
        timer_disable(cpu_id);
    od
}

// `main()` in kernel/src/main.rs
proctype primary_main() {
    do
    :: true ->
        sleep(0);
        timer_disable(0);

        wake_workers(0);
    od
}

proctype timer(byte cpu_id) {
    do
    :: d_step { timer_enable[cpu_id] == 1 && timer_interrupt[cpu_id] == 0 ->
            timer_interrupt[cpu_id] = 1;
    }
    od
}

init {
    byte i;

    for (i: 0 .. CPU_NUM - 1) {
        CPU_SLEEP_TAG[i] = Idle;
        interrupt_mask[i] = 1;
        IPI[i] = 0;
        timer_enable[i] = 0;
        timer_interrupt[i] = 0;
    }

    for (i: 0 .. CPU_NUM - 1) {
        run timer(i);
    }

    run primary_main();

    for (i: 0 .. WORKERS - 1) {
        run run_main(i + 1);
    }
}

ltl eventually_execute  {
    <>[] (run_queue == 0)
}
