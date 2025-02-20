#define QUEUE_LEN 1
#define NUM_SEND 2
#define NUM_RX_TASK 2
#define NUM_QUEUE 2

#define NUM_PROC (NUM_RX_TASK + NUM_SEND)

#include "../../../../awkernel_async_lib/src/task/cooperative_spin/fair_lock.pml"

chan UDP_Rx = [QUEUE_LEN] of { int };

FairLock LockRxRingq[NUM_QUEUE];
FairLock LockTxRingq[NUM_QUEUE];
FairLock LockInner;

bool set[NUM_SEND];

inline interface_poll(ch, tmp) {
    atomic {
        do
            :: len(UDP_Rx) > 0 ->
                UDP_Rx ? tmp;
                ch ! tmp;
            :: else ->
                break;
        od;
    }
}

inline tx(ch, tmp) {
    atomic {
        do
            :: len(ch) > 0 ->
                ch ? tmp;
                set[tmp] = true;
                printf("set[%d] = %d\n", tmp, set[tmp]);
            :: else ->
                break;
        od;
    }
}

inline rnd(r) {
    if
    :: r = 0
    :: r = 1;
    fi;
}

// Modeling `awkernel_lib::net::if_net::IfNet::poll_rx()`.
proctype poll_rx(int tid) {
    chan ch = [QUEUE_LEN] of { int };
    int tmp;

    int rxq;
    int txq;

    atomic {
        rnd(rxq);
        rnd(txq);
    }

    lock(tid, LockRxRingq[rxq]);
    lock(tid, LockTxRingq[txq]);

    lock(tid, LockInner);
    interface_poll(ch, tmp);
    unlock(tid, LockInner);

    tx(ch, tmp);

    unlock(tid, LockTxRingq[txq]);
    unlock(tid, LockRxRingq[rxq]);
}

// Modeling `awkernel_lib::net::if_net::IfNet::poll_tx_only()`.
proctype poll_tx_only(int tid) {
    chan ch = [QUEUE_LEN] of { int };
    int tmp;

    int txq;
    rnd(txq);

    lock(tid, LockTxRingq[txq]);

    lock(tid, LockInner);
    interface_poll(ch, tmp);
    unlock(tid, LockInner);

    tx(ch, tmp);

    unlock(tid, LockTxRingq[txq]);
}

init {
    int i = 0;
    int tid = 0;

    for (i: 0 .. NUM_SEND - 1) {
        set[i] = false;
    }

    // create receive tasks
    for (i: 0 .. NUM_RX_TASK - 1) {
        run poll_rx(tid);
        tid++;
    }

    // send NUM_SEND packets
    for (i: 0 .. NUM_SEND - 1) {
        UDP_Rx ! i;
        run poll_tx_only(tid);
        tid++;
    }
}

ltl eventually_all_true {
    <> (set[0] && set[1]) && [] ((set[0] && set[1]) -> [] (set[0] && set[1]))
}
