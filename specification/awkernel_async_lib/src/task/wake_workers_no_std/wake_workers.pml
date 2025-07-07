#define WORKERS 2
#define TASK_NUM (WORKERS + 1)
#define CPU_NUM (WORKERS + 1)
#define TIMEOUT_NONE false
#define TIMEOUT_SOME true

mtype = { Active, Waiting, Waking }
mtype CPU_SLEEP_TAG[CPU_NUM]

bool interrupt_mask[CPU_NUM]
bool IPI[CPU_NUM]             // edge-trigger interrupt
bool timer_enable[CPU_NUM]
bool timer_interrupt[CPU_NUM] // level-sensitive interrupt

chan run_queue = [TASK_NUM] of { byte } // run queue

byte task_id = 1
byte num_blocking = 0
byte created_task = 0

chan delta_list = [TASK_NUM] of { byte } // delta list

bool task_need_sleep[TASK_NUM + 1] = true

byte finished_tasks = 0

inline compare_exchange(target, current, new, prev)
{
    d_step {
        prev = target
        if
        :: target == current ->
            target = new
        :: else
        fi
    }
}

inline send_ipi(cpu_id) {
    if
    :: d_step {
        interrupt_mask[cpu_id] == false ->
        IPI[cpu_id] = true
        printf("send IPI to CPU#{%d}, interrupt_mask[%d] = %d\n", cpu_id, cpu_id, interrupt_mask[cpu_id])
    }
    :: else
    fi
}

inline interrupt_handler(cpu_id) {
    // disable interrupts
    if
    :: d_step {
        interrupt_mask[cpu_id] == false -> interrupt_mask[cpu_id] = true
    }
    :: else -> goto return_interrupt_handler
    fi

    // handle IPI
    d_step {
        if
        :: IPI[cpu_id] == true ->
            IPI[cpu_id] = false
            printf("CPU#{%d}: handle IPI\n", cpu_id)
        :: else
        fi

        // handle timer interrupt
        if
        :: timer_enable[cpu_id] == true && timer_interrupt[cpu_id] == true ->
            timer_interrupt[cpu_id] = false
            printf("CPU#{%d}: handle timer interrupt\n", cpu_id)
        :: else
        fi
    }

    // Enable timer.
    // `handle_irqs() and `handle_irq()` in awkernel_lib/src/interrupt.rs.
    // `reset_wakeup_timer()` in awkernel_lib/src/cpu/sleep_cpu_no_std.rs.
    if
    :: CPU_SLEEP_TAG[cpu_id] == Waiting -> timer_reset(cpu_id)
    :: else
    fi

    // enable interrupts
    interrupt_mask[cpu_id] = false
return_interrupt_handler:
}

inline wait_interrupt(cpu_id) {
    assert(interrupt_mask[cpu_id] == false)
    if
    :: (timer_enable[cpu_id] == true && timer_interrupt[cpu_id] == true)
    :: d_step { IPI[cpu_id] -> IPI[cpu_id] = false }
    fi
}

inline rnd4(rnd) {
    if
    :: rnd = 0
    :: rnd = 1
    :: rnd = 2
    :: rnd = 3
    fi
}

// `SleepCpuNoStd::sleep()` in awkernel_lib/src/cpu/sleep_cpu_no_std.rs
inline sleep(cpu_id, tout) {
    if
    :: tout != TIMEOUT_NONE ->
        // enable timer
        timer_reset(cpu_id)
    :: else
    fi

    // if wake-up already pending, consume and return
    if
    :: CPU_SLEEP_TAG[cpu_id] == Waking -> goto return_sleep2
    :: else
    fi

    byte rnd // chose the position interrupts occur
    d_step {
        // enable interrupts and halt until IPI arrives
        interrupt_mask[cpu_id] = false
        rnd4(rnd)
    }

    // receive interrupts
    if
    :: rnd == 0 -> interrupt_handler(cpu_id)
    :: else
    fi

    // mark waiting before halt
    mtype prev_val
    compare_exchange(CPU_SLEEP_TAG[cpu_id], Active, Waiting, prev_val)

    if
    :: prev_val == Active
    :: prev_val == Waking -> goto return_sleep1
    :: else -> assert(prev_val != Waiting) // unreachable!()
    fi

    // receive interrupts
    if
    :: rnd == 1 -> interrupt_handler(cpu_id)
    :: else
    fi

    // Because x86 APIC timers are edge-triggered interrupts,
    // timer interrupts that occur during interrupt handlers (when interrupts are disabled)
    // will be lost.
    // Therefore, the timeout is checked here.
    if
    :: tout != TIMEOUT_NONE ->
        if
        :: true ->
            // timeout <= elapsed
            CPU_SLEEP_TAG[cpu_id] = Active
            goto return_sleep3
        :: true
        fi
    :: else
    fi

    // In case that there are any tasks to run,
    // wake up the primary CPU to wake me up.
    byte tmp
    wake_up(cpu_id, 0, tmp)

    // receive interrupts
    if
    :: rnd == 2 -> interrupt_handler(cpu_id)
    :: else
    fi

    compare_exchange(CPU_SLEEP_TAG[cpu_id], Waking, Active, prev_val)

    if
    :: prev_val == Waking ->
        interrupt_mask[cpu_id] = true
        goto return_sleep3
    :: prev_val == Waiting
    :: else -> assert(false) // unreachable!()
    fi

    // Rare Case:
    //   IPIs sent during interrupt handlers invoked here will be ignored because IPIs are edge-trigger.
    //   To notify it again, Awkernel setup a timer by `reset_wakeup_timer()` in interrupt handlers.

    // receive interrupts
    if
    :: rnd == 3 -> interrupt_handler(cpu_id)
    :: else
    fi

    wait_interrupt(cpu_id)

    interrupt_handler(cpu_id)

return_sleep1:
    // disable interrupts
    interrupt_mask[cpu_id] = true

return_sleep2:
    CPU_SLEEP_TAG[cpu_id] = Active

return_sleep3:
    timer_disable(cpu_id)
}

// `SleepCpuNoStd::wake_up()` in awkernel_lib/src/cpu/sleep_cpu_no_std.rs
inline wake_up(my_id, target_cpu_id, result) {
    if
    :: atomic { my_id == target_cpu_id ->
        result = false
        goto return_wake_up
    }
    :: else
    fi

    // attempt state transitions until success or redundant
    if
    :: atomic { CPU_SLEEP_TAG[target_cpu_id] == Active ->
        // CPU not yet sleeping: schedule wake-up
        CPU_SLEEP_TAG[target_cpu_id] = Waking
        result = false
        printf("Active -> Waking: CPU#{%d}", target_cpu_id)
    }
    :: atomic { CPU_SLEEP_TAG[target_cpu_id] == Waiting ->
         // CPU is halted: send IPI
        CPU_SLEEP_TAG[target_cpu_id] = Waking
        result = true
        printf("Waiting -> Waking: CPU#{%d}", target_cpu_id)
    }
        send_ipi(target_cpu_id)
    :: atomic { CPU_SLEEP_TAG[target_cpu_id] == Waking ->
        // wake-up already pending
        printf("already waking: CPU#{%d}", target_cpu_id)
        result = false
    }
        send_ipi(target_cpu_id)
    fi

return_wake_up:
}

// `wake_workers()` in awkernel_async_lib/src/task.rs
inline wake_workers(cpu_id) {
    byte num_tasks = len(run_queue)
    byte i
    bool result

    for (i: 1 .. CPU_NUM - 1) {
        if
        :: num_tasks == 0 -> break
        :: else ->
            wake_up(cpu_id, i, result)

            if
            :: d_step { result == true ->
                printf("wake_up(%d)\n", i)
                num_tasks--
            }
            :: else
            fi
        fi
    }
}

inline timer_reset(cpu_id) {
    d_step {
        printf("CPU#{%d}: reset timer\n", cpu_id)
        timer_enable[cpu_id] = true
    }
}

inline timer_disable(cpu_id) {
    d_step {
        printf("CPU#{%d}: disable timer\n", cpu_id)
        timer_enable[cpu_id] = false
    }
}

inline spawn_task() {
    byte tmp
    d_step {
        run_queue ! task_id
        printf("spawn_task: task_id = %d, len(run_queue) = %d\n", task_id, len(run_queue))
        task_id++
    }
    wake_up(CPU_NUM, 0, tmp)
}

// Simulate tasks
inline task_poll(tid) {
    bool result

    // spawn a new task
    // `Task::wake()` in awkernel_async_lib/src/task.rs
    do
    :: d_step { created_task < TASK_NUM ->
        created_task++
    }
        spawn_task()
    :: break
    od

    // Simulate blocking tasks.
    // Even if there are `WORKERS - 1` blocking tasks,
    // every task will be woken up.
    if
    :: d_step { num_blocking < WORKERS - 1 ->
        num_blocking++
        printf("block: num_blocking = %d, cpu_id = %d\n", num_blocking, cpu_id)
    }
        false // block
        assert(false)
    :: true
    fi

    d_step {
        if
        :: task_need_sleep[tid] ->
            task_need_sleep[tid] = false
            delta_list ! tid // sleeping
        :: else -> finished_tasks++
            printf("task_poll: tid = %d, finished_tasks = %d\n", tid, finished_tasks)
            if
            :: finished_tasks + num_blocking == TASK_NUM ->
                printf("All tasks finished.\n")
            :: else
            fi
        fi
    }

}

// Wake up sleeping tasks.
// `wake_task()` in awkernel_async_lib/src/scheduler.rs
inline wake_task(time_to_wait) {
    byte tid;
    d_step {
        if
        :: len(delta_list) > 0 ->
            delta_list ? tid
            run_queue ! tid
            printf("wake_task: tid = %d, len(run_queue) = %d, len(delta_list) = %d\n", tid, len(run_queue), len(delta_list))
            time_to_wait = TIMEOUT_SOME
        :: else ->
            time_to_wait = TIMEOUT_NONE
        fi
    }
}

inline get_next_task(tid) {
    if
    :: d_step {
        len(run_queue) > 0 ->
        run_queue ? tid
        printf("get_next_task: tid = %d, len(run_queue) = %d\n", tid, len(run_queue))
    }
    :: else ->
        tid = 0
    fi
}

// `run_main()` in awkernel_async_lib/src/task.rs
proctype run_main(byte cpu_id) {
    byte tid
    do
    :: get_next_task(tid)
        if
        :: tid > 0 -> task_poll(tid)
        :: else -> sleep(cpu_id, TIMEOUT_NONE)
        fi
    od
}

// `main()` in kernel/src/main.rs
proctype primary_main() {
    bool time_to_wait;
    do
    :: true ->
        wake_task(time_to_wait)
        sleep(0, time_to_wait)
        wake_workers(0)
    od
}

proctype timer(byte cpu_id) {
    do
    :: d_step {
        timer_enable[cpu_id] == true && timer_interrupt[cpu_id] == false ->
        timer_interrupt[cpu_id] = true
    }
    od
}

init {
    byte i

    for (i: 0 .. CPU_NUM - 1) {
        CPU_SLEEP_TAG[i] = Active
        interrupt_mask[i] = true
        IPI[i] = false
        timer_enable[i] = false
        timer_interrupt[i] = false
    }

    created_task++
    spawn_task()

    for (i: 0 .. CPU_NUM - 1) {
        run timer(i)
    }

    run primary_main()

    for (i: 0 .. WORKERS - 1) {
        run run_main(i + 1)
    }
}

ltl eventually_execute  {
    <>[] (len(run_queue) == 0)
}
