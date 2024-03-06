#define TASK_NUM 4
#define WORKERS 2

mtype = { Ready, Running, Waiting, Terminated, Pending };

mtype state = Ready;

// awkernel_async_lib::task::TaskInfo
typedef TaskInfo {
    mtype state;
    bool in_queue;
    bool need_sched;
    bool is_terminated;
    int id;
};

TaskInfo tasks[TASK_NUM];

// Queue of the FIFO scheduler
chan queue = [TASK_NUM * 2] of { int };

bool lock_info[TASK_NUM];
bool lock_future[TASK_NUM];
bool lock_scheduler = false;

bool result_try_lock[WORKERS];
int result_next[WORKERS];
mtype result_future[WORKERS];

bool wake_other[TASK_NUM / 2];

int num_terminated = 0;

inline try_lock(tid, mutex) {
    atomic {
        if
            :: mutex == false ->
                mutex = true;
                result_try_lock[tid] = true;
            :: mutex == true -> result_try_lock[tid] = false;
        fi
    }
}

inline lock(mutex) {
    atomic {
        mutex == false -> mutex = true
    }
}

inline unlock(mutex) {
    mutex = false
}

// awkernel_async_lib::scheduler::fifo::FIFOScheduler::wake_task()
inline wake_task(task) {
    lock(lock_scheduler);
    lock(lock_info[task]);

    tasks[task].in_queue = true;
    unlock(lock_info[task]);
    queue ! task;
    unlock(lock_scheduler);
}

// wkernel_async_lib::task::ArcWake::wake()
inline wake(task) {
    lock(lock_info[task]);

    if
        :: tasks[task].state == Running ->
            tasks[task].need_sched = true;
            printf("wake(): task = %d, state = %d\n", task, tasks[task].state);
            unlock(lock_info[task]);
            wake_task(task);
        :: tasks[task].state == Terminated || tasks[task].in_queue -> unlock(lock_info[task]);
        :: else ->
            printf("wake(): task = %d, state = %d\n", task, tasks[task].state);
            unlock(lock_info[task]);
            wake_task(task);
    fi
}

// awkernel_async_lib::scheduler::fifo::FIFOScheduler::get_next()
inline get_next(tid) {
    lock(lock_scheduler);

    int head;

start_get_next:

    if
        :: atomic { queue ? [head] -> queue ? head };
            lock(lock_info[head]);

            if
                :: tasks[head].state == Terminated ->
                    unlock(lock_info[head]);
                    goto start_get_next;
                :: else -> skip;
            fi

            tasks[head].in_queue = false;
            tasks[head].state = Running;

            printf("Running: task = %d, state = %d\n", head, tasks[head].state);

            unlock(lock_info[head]);
            unlock(lock_scheduler);

            result_next[tid] = head;
        :: else ->
            unlock(lock_scheduler);
            result_next[tid] = -1;
    fi
}

// If there is 2 tasks, and their task ID's are 0 and 1.
// This future will execute as follows.
//
// step1: Task 0 wakes Task 1 up, and returns "Pending".
// step2: Task 1 wakes Task 0 up, and returns "Ready".
// step3: Task 0 returns "Ready".
//
// A task will become "Terminated", after returning "Ready".
inline future(tid, task) {
    if
        :: task >= TASK_NUM / 2 ->
            wake(task - TASK_NUM / 2);
            result_future[tid] = Ready;
        :: else ->
            if
                :: wake_other[task] ->
                    // wake(task);
                    result_future[tid] = Ready;
                    printf("future(): tid = %d, task = %d\n", tid, task);
                :: else ->
                    wake(task + TASK_NUM / 2);
                    wake_other[task] = true;
                    result_future[tid] = Pending;
            fi
    fi
}

proctype run_main(int tid) {
start:
    if
        :: num_terminated == TASK_NUM -> goto end;
        :: else -> skip;
    fi

    get_next(tid);

    int task = result_next[tid];

    if
        :: task == -1 -> goto end;
        :: else -> skip;
    fi

    try_lock(tid, lock_future[task]);

    if
        :: result_try_lock[tid] == false ->
            // This task is running on another CPU,
            // and re-schedule the task to avoid starvation just in case.
            wake(task);
            goto start;
        :: else -> skip;
    fi

    // Can remove this?
    if
        :: tasks[task].is_terminated ->
            unlock(lock_future[task]);
            goto start;
        :: else -> skip;
    fi

    lock(lock_info[task]);

    if
        :: tasks[task].state == Terminated ->
            unlock(lock_info[task]);
            unlock(lock_future[task]);
            goto start;
        :: else -> skip;
    fi

    unlock(lock_info[task]);

    tasks[task].need_sched = false;

    printf("execute task = %d\n", task);

    // Invoke a task.
    future(tid, task);

    unlock(lock_future[task]);

    lock(lock_info[task]);

    if
        :: result_future[tid] == Pending ->
            printf("Pending: tid = %d\n", tid);
        :: result_future[tid] == Ready ->
            printf("Ready: tid = %d\n", tid);
    fi

    if
        :: result_future[tid] == Pending ->
            tasks[task].state = Waiting;

            printf("Waiting: task = %d, state = %d\n", task, tasks[task].state);

            if
                :: tasks[task].need_sched ->
                    tasks[task].need_sched = false;
                    unlock(lock_info[task]);
                    wake_task(task);
                    goto start;
                :: else -> skip;
            fi
        :: result_future[tid] == Ready ->
            if
                :: tasks[task].state != Terminated ->
                    num_terminated++;
                :: else -> skip;
            fi

            tasks[task].state = Terminated;
            tasks[task].is_terminated = true;

            printf("Terminated: task = %d, state = %d, num_terminated = %d,\n", task, tasks[task].state, num_terminated);
    fi

    unlock(lock_info[task]);

    goto start;

end:
}

init {
    int i;

    for (i: 0 .. TASK_NUM / 2 - 1) {
        wake_other[i] = false;
    }

    lock_scheduler = false;

    for (i: 0 .. TASK_NUM - 1) {
        tasks[i].id = i;
        tasks[i].state = Ready;
        tasks[i].in_queue = false;
        tasks[i].need_sched = false;
        tasks[i].is_terminated = false;

        lock_info[i] = false;
        lock_future[i] = false;

        printf("tasks[%d].state = %d\n", i, tasks[i].state);

        wake(i);
    }

    for (i: 0 .. WORKERS - 1) {
        run run_main(i);
    }
}

// - starvation-free
// - eventually all tasks will be terminated
ltl p0  {
    <> (num_terminated == TASK_NUM)
}
