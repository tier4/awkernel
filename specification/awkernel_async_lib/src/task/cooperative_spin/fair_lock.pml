// #define NUM_PROC 2

typedef FairLock {
    bool is_locked;
    bool flag[NUM_PROC];
    chan request = [NUM_PROC - 1] of { int };
};

FairLock lock_for_test;

int num_lock = 0;
bool is_fair = false;

bool result_try_lock[NUM_PROC];

inline lock(tid, mutex) {
    bool need_wait = false;
    if
        :: atomic {
            mutex.is_locked ->
            assert(!mutex.request ? [tid]);  // Deadlock
            mutex.flag[tid] = false;
            mutex.request ! tid;
            need_wait = true;
        }
        :: atomic {
            !mutex.is_locked ->
            mutex.is_locked = true;
        }
    fi;

    if
        :: need_wait ->
            mutex.flag[tid];
        :: else -> skip;
    fi
}

inline try_lock(tid, mutex) {
    if
        :: atomic {
            mutex.is_locked ->
            result_try_lock[tid] = false;
        }
        :: atomic {
            !mutex.is_locked ->
            mutex.is_locked = true;
            result_try_lock[tid] = true;
        }
    fi;
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

inline test_fair_mutex() {
    run proc0(0);
    run proc1(1);
}

proctype proc0() {
    int tid = 0;

    do
        :: lock(tid, lock_for_test) ->
            num_lock++;
            num_lock--;
            unlock(tid, lock_for_test);
    od
}

proctype proc1() {
    int tid = 1;
    lock(tid, lock_for_test);
    num_lock++;
    num_lock--;
    unlock(tid, lock_for_test);

    is_fair = true;
}

// ltl mutual_exclusion { [] (num_lock <= 1) }
// ltl fair { []<> is_fair }
