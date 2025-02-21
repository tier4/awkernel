#define QUEUE_LEN 1
#define NUM_SEND 2
#define NUM_RX_TASK 2
#define NUM_QUEUE 2

#define NUM_PROC (NUM_RX_TASK + NUM_SEND)

#include "../../../../awkernel_async_lib/src/task/cooperative_spin/fair_lock.pml"

// The transmission queue of the TCP/IP stack.
// Userland applications send packets to this queue,
// and the TCP/IP stack receives packets from this queue for sending packets.
chan IP_Tx = [QUEUE_LEN] of { int };

FairLock LockRxRingq[NUM_QUEUE];
FairLock LockTxRingq[NUM_QUEUE];
FairLock LockInner;

// This array is used to check if all packets are sent.
bool set[NUM_SEND];

// The number of processes that will poll packets.
int will_poll = 0;

// Poll packets from the TCP/IP stack.
inline interface_poll(ch, tmp) {
    atomic {
        do
            :: len(IP_Tx) > 0 ->
                IP_Tx ? tmp;
                ch ! tmp;
            :: else ->
                break;
        od;
    }
}

// Send packets in `ch` to the network.
// This function simulates the behavior of the network interface.
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

// Generate a random number.
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

    // Randomly select a reception queue and a transmission queue.
    atomic {
        rnd(rxq);
        rnd(txq);
    }

    will_poll++;;

    lock(tid, LockRxRingq[rxq]);
    lock(tid, LockTxRingq[txq]);

    lock(tid, LockInner);
    will_poll--;
    interface_poll(ch, tmp);
    unlock(tid, LockInner);

    tx(ch, tmp);

    unlock(tid, LockTxRingq[txq]);
    unlock(tid, LockRxRingq[rxq]);
}

// Modeling `awkernel_lib::net::if_net::IfNet::poll_tx_only()`.
proctype poll_tx_only(int tid, send_data) {
    chan ch = [QUEUE_LEN] of { int };
    int tmp;

    int txq;
    rnd(txq); // Randomly select a transmission queue.

    IP_Tx ! send_data; // Send an IP packet.

    // If some process will poll, this process need not to poll.
    atomic {
        if
            :: will_poll > 0 -> goto end;
            :: else -> will_poll++;
        fi;
    }

    lock(tid, LockTxRingq[txq]);

    lock(tid, LockInner);
    will_poll--;
    interface_poll(ch, tmp);
    unlock(tid, LockInner);

    tx(ch, tmp);

    unlock(tid, LockTxRingq[txq]);
end:
}

init {
    int i = 0;
    int tid = 0;

    for (i: 0 .. NUM_SEND - 1) {
        set[i] = false;
    }

    // Create receive tasks.
    for (i: 0 .. NUM_RX_TASK - 1) {
        run poll_rx(tid);
        tid++;
    }

    // Create send tasks.
    for (i: 0 .. NUM_SEND - 1) {
        run poll_tx_only(tid, i);
        tid++;
    }
}

ltl eventually_all_true {
    <> (set[0] && set[1]) && [] ((set[0] && set[1]) -> [] (set[0] && set[1]))
}
