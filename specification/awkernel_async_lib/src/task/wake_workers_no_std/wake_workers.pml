#define WORKERS 2
#define TASK_NUM (WORKERS + 1)
#define CPU_NUM (WORKERS + 1)

mtype = { Active, Waiting, Waking };
mtype CPU_SLEEP_TAG[CPU_NUM];

bool interrupt_mask[CPU_NUM];
bool IPI[CPU_NUM];             // edge-trigger interrupt
bool timer_enable[CPU_NUM];
bool timer_interrupt[CPU_NUM]; // level-sensitive interrupt

byte run_queue = 1;
byte num_blocking = 0;
byte created_task = 1;

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
        :: interrupt_mask[cpu_id] == false -> IPI[cpu_id] = true;
        :: else
        fi
    }
}

inline interrupt_handler(cpu_id) {
    // disable interrupts
    atomic {
        if
        :: interrupt_mask[cpu_id] == false -> interrupt_mask[cpu_id] = true;
        :: else -> goto return_interrupt_handler;
        fi
    }

    d_step {
        // handle IPI
        if
        :: IPI[cpu_id] == true ->
            IPI[cpu_id] = false;
            printf("CPU#{%d}: handle IPI\n", cpu_id);
        :: else
        fi
    }

    d_step {
        // handle timer interrupt
        if
        :: timer_enable[cpu_id] == true && timer_interrupt[cpu_id] == true ->
            timer_interrupt[cpu_id] = false;
            printf("CPU#{%d}: handle timer interrupt\n", cpu_id);
        :: else
        fi
    }

    d_step {
        // Enable timer.
        // `handle_irqs() and `handle_irq()` in awkernel_lib/src/interrupt.rs.
        // `reset_wakeup_timer()` in awkernel_lib/src/cpu/sleep_cpu_no_std.rs.
        if
        :: CPU_SLEEP_TAG[cpu_id] == Waiting -> timer_reset(cpu_id)
        :: else
        fi
    }

    // enable interrupts
    interrupt_mask[cpu_id] = false;
return_interrupt_handler:
}

inline wait_interrupt(cpu_id) {
    assert(interrupt_mask[cpu_id] == false);
    if
    :: (timer_enable[cpu_id] == true && timer_interrupt[cpu_id] == true)
    :: IPI[cpu_id] -> IPI[cpu_id] = false
    fi
}

inline rnd5(rnd) {
    if
    :: rnd = 0
    :: rnd = 1
    :: rnd = 2
    :: rnd = 3
    :: rnd = 4
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
        interrupt_mask[cpu_id] = false;
        rnd5(rnd);
    }

    // receive interrupts
    if
    :: rnd == 0 -> interrupt_handler(cpu_id)
    :: else
    fi

    // mark waiting before halt
    mtype prev_val;
    compare_exchange(CPU_SLEEP_TAG[cpu_id], Active, Waiting, prev_val);

    if
    :: prev_val == Active
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


    compare_exchange(CPU_SLEEP_TAG[cpu_id], Waking, Active, prev_val);

    if
    :: prev_val == Waking ->
        interrupt_mask[cpu_id] = true;
        goto return_sleep3;
    :: prev_val == Waiting
    :: else -> assert(false); // unreachable!()
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
    interrupt_mask[cpu_id] = true;

return_sleep2:
    CPU_SLEEP_TAG[cpu_id] = Active;

return_sleep3:
}

// `SleepCpuNoStd::wake_up()` in awkernel_lib/src/cpu/sleep_cpu_no_std.rs
inline wake_up(my_id, target_cpu_id, result) {
    if
    :: atomic { my_id == target_cpu_id ->
        result = false;
        goto return_wake_up;
    }
    :: else
    fi

    // attempt state transitions until success or redundant
    if
    :: atomic { CPU_SLEEP_TAG[target_cpu_id] == Active ->
        // CPU not yet sleeping: schedule wake-up
        CPU_SLEEP_TAG[target_cpu_id] = Waking;
        result = false;
        printf("Active -> Waking: CPU#{%d}", target_cpu_id);
    }
    :: atomic { CPU_SLEEP_TAG[target_cpu_id] == Waiting ->
         // CPU is halted: send IPI
        CPU_SLEEP_TAG[target_cpu_id] = Waking;
        result = true;
        printf("Waiting -> Waking: CPU#{%d}", target_cpu_id);
    }
        send_ipi(target_cpu_id);
    :: atomic { CPU_SLEEP_TAG[target_cpu_id] == Waking ->
        // wake-up already pending
        printf("already waking: CPU#{%d}", target_cpu_id);
        result = false;
    }
        send_ipi(target_cpu_id);
    fi

return_wake_up:
}

// `wake_workers()` in awkernel_async_lib/src/task.rs
inline wake_workers(cpu_id) {
    byte num_tasks = run_queue;
    byte i;
    bool result;

    for (i: 1 .. CPU_NUM - 1) {
        if
        :: num_tasks == 0 -> break;
        :: else ->
            wake_up(cpu_id, i, result);

            if
            :: d_step { result == true ->
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
    timer_enable[cpu_id] = true;
}

inline timer_disable(cpu_id) {
    d_step {
        printf("CPU#{%d}: disable timer\n", cpu_id);
        timer_enable[cpu_id] = false;
    }
}

// Simulate tasks
inline task_poll() {
    bool result;

    // spawn a new task
    // `Task::wake()` in awkernel_async_lib/src/task.rs
    do
    :: atomic { created_task < TASK_NUM ->
        created_task++;
        run_queue++;
    }
        wake_up(CPU_NUM, 0, result);
    :: break
    od

    // Simulate blocking tasks.
    // Even if there are `WORKERS - 1` blocking tasks,
    // every task will be woken up.
    if
    :: d_step { num_blocking < WORKERS - 1 ->
        num_blocking++;
        printf("num_blocking = %d, cpu_id = %d\n", num_blocking, cpu_id);
    }
        false; // block
        assert(false);
    :: skip
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
    :: d_step { timer_enable[cpu_id] == true && timer_interrupt[cpu_id] == false ->
            timer_interrupt[cpu_id] = true;
    }
    od
}

init {
    byte i;

    for (i: 0 .. CPU_NUM - 1) {
        CPU_SLEEP_TAG[i] = Active;
        interrupt_mask[i] = true;
        IPI[i] = false;
        timer_enable[i] = false;
        timer_interrupt[i] = false;
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
