mtype = { grant }; // notification

bool mutex[WORKERS] = false;
chan cond[WORKERS] = [1] of { mtype };  // channel for condition wait and notify

// Mutex lock
inline lock(cpu_id) {
    do
    :: atomic { mutex[cpu_id - 1] == false -> mutex[cpu_id - 1] = true; break; }
    od
}

// Mutex unlock
inline unlock(cpu_id) {
    mutex[cpu_id - 1] = false;
}

// Wait for condition
inline cond_wait(cpu_id) {
    unlock(cpu_id);
    do
    :: atomic { len(cond[cpu_id - 1]) != 0 && mutex[cpu_id - 1] == false ->
        cond[cpu_id - 1] ? grant;
        mutex[cpu_id - 1] = true;
        break;
    }
    od
}

// Notify one waiting thread
inline cond_notify_one(cpu_id) {
    if
    :: d_step { len(cond[cpu_id - 1]) == 0 ->
        cond[cpu_id - 1] ! grant;
    }
    :: else -> skip;
    fi
}