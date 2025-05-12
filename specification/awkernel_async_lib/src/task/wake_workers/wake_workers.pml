#define WORKERS 3
#define TASK_NUM (WORKERS + 1)

#include "mutex.pml"

mtype = { eventfd };
chan epoll = [1] of { mtype };

int run_queue = 0;
bool is_awake[WORKERS];
bool is_wake_up[WORKERS];

int num_blocking = 0;

// `SleepCpuStd::sleep()` in awkernel_lib/src/cpu/sleep_cpu_std.rs
inline sleep(cpu_id) {
    assert(cpu_id != 0);

    lock(cpu_id);

    if
    :: is_wake_up[cpu_id - 1] -> goto awake;
    :: else
    fi

    is_awake[cpu_id - 1] = false;
    select_notify();

    do
    :: true ->
        cond_wait(cpu_id);
        if
        :: is_wake_up[cpu_id - 1] ->
            is_awake[cpu_id - 1] = true;
            is_wake_up[cpu_id - 1] = false;
            goto awake;
        :: else
        fi
    od

awake:
    unlock(cpu_id);
}

// `SleepCpuStd::wake_up()` in awkernel_lib/src/cpu/sleep_cpu_std.rs
inline wake_up(cpu_id, result) {
    if
    :: cpu_id == 0 ->
        select_notify();
        result = true;
        goto finish_wake_up2;
    :: else
    fi

    lock(cpu_id);

    if
    :: is_awake[cpu_id - 1] -> {
        result = false;
        goto finish_wake_up1;
    }
    :: else
    fi

    is_wake_up[cpu_id - 1] = true;
    cond_notify_one(cpu_id);
    result = true;

finish_wake_up1:
    unlock(cpu_id);
finish_wake_up2:
}

// `wake_workers()` in awkernel_async_lib/src/task.rs
inline wake_workers() {
    int num_tasks = run_queue;
    int num_cpu = WORKERS + 1;
    int i;
    bool result;

    for (i: 1 .. num_cpu - 1) {
        if
        :: num_tasks == 0 -> break;
        :: else ->
            wake_up(i, result);

            if
            :: result == true ->
                d_step {
                    printf("wake_up(%d)\n", i);
                    num_tasks--;
                }
            :: else
            fi
        fi
    }
}

// `wait()` in awkernel_lib/src/select.rs
inline select_wait() {
    if
    :: atomic { len(epoll) > 0 -> epoll ? eventfd };
    fi
}

// `notify()` in awkernel_lib/src/select.rs
inline select_notify() {
    if
    :: d_step { len(epoll) == 0 -> epoll ! eventfd };
    :: else
    fi
}

// Simulate tasks
inline task_poll() {
    if
    :: true ->
        if
        // Simulate blocking tasks.
        // Even if there are `WORKERS - 1` blocking tasks,
        // every task will be woken up.
        :: atomic { num_blocking < WORKERS - 1 ->
            num_blocking++;
            printf("num_blocking = %d, cpu_id = %d\n", num_blocking, cpu_id);
        }
            if
            :: false // block
            fi
            assert(false);
        :: else
        fi
    :: true
    fi
}

// `run_main()` in awkernel_async_lib/src/task.rs
proctype run_main(int cpu_id) {
    do
    :: d_step { run_queue > 0 ->
        run_queue--;
        printf("run_queue--: run_queue = %d\n", run_queue);
    };
        task_poll();
    :: else ->
        printf("run_queue == 0: run_queue = %d\n", run_queue);
        sleep(cpu_id);
    od
}

// `main()` in kernel/src/main.rs
proctype primary_main() {
    do
    :: true ->
        select_wait();
        wake_workers();
    od
}

// `Task::wake()` in awkernel_async_lib/src/task.rs
proctype spawn_tasks() {
    int i;
    bool result;

    for (i: 0 .. TASK_NUM - 1) {
        d_step {
            run_queue++;
            printf("run_queue++: run_queue = %d\n", run_queue);
        }
        wake_up(0, result);
    }
}

init {
    int i;

    for (i: 0 .. WORKERS - 1) {
        is_awake[i] = true;
        is_wake_up[i] = false;
    }

    run primary_main();

    for (i: 0 .. WORKERS - 1) {
        run run_main(i + 1);
    }

    run spawn_tasks();
}

ltl eventually_execute  {
    <>[] (run_queue == 0)
}
