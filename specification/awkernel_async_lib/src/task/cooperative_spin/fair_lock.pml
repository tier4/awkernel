#define NUM_PROC 2

typedef FairLock {
    bool is_locked;
    bool flag[NUM_PROC];
    chan request = [NUM_PROC] of { int };
};

FairLock global_lock;

inline lock(tid, mutex) {
    atomic {
        if
            :: mutex.is_locked ->
                mutex.flag[tid] = false;
                mutex.request ! tid;
            :: else ->
                mutex.is_locked = true;
        fi;
    }
}

inline unlock(tid, mutex) {
    atomic {
        int p;
        if
            :: mutex.request ? [p] ->
                mutex.request ? p;
                mutex.flag[p] = true;
            :: else ->
                mutex.is_locked = false;
        fi;
    }
}

active proctype proc0(int tid) {
    lock(tid, global_lock);

    unlock(tid, global_lock);
}

active [NUM_PROC] proctype proc1(int tid) {
    lock(tid, global_lock);

    unlock(tid, global_lock);
}
