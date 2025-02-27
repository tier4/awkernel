#define QUEUE_SIZE 2
#define NUM_SEND 2
#define NUM_RX_TASK 1
#define NUM_QUEUE 2

#define NUM_PROC (NUM_RX_TASK + NUM_SEND)

#include "../../../../awkernel_async_lib/src/task/cooperative_spin/fair_lock.pml"

// The transmission queue of the TCP/IP stack.
// Userland applications send packets to this queue,
// and the TCP/IP stack receives packets from this queue for sending packets.
chan IP_Tx = [QUEUE_SIZE] of { int };

FairLock LockRxRingq[NUM_QUEUE];
FairLock LockTxRingq[NUM_QUEUE];
FairLock LockInner;

// This array is used to check if all packets are sent.
bool set[NUM_SEND];

// The number of processes that will poll packets.
int will_poll = 0;

// Poll packets from the TCP/IP stack.
inline interface_poll(ch, tmp, result) {
    result = false;

    atomic {
        do
            :: full(ch) -> break;
            :: empty(IP_Tx) -> break;
            :: nfull(ch) && nempty(IP_Tx) ->
                IP_Tx ? tmp;
                ch ! tmp;
                result = true;
        od;
    }
}

// Send packets in `ch` to the network.
// This function simulates the behavior of the network interface.
inline net_device_send(ch, tmp) {
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

// Modeling `awkernel_lib::net::if_net::IfNet::poll_rx_tx()`.
proctype poll_rx_tx(int tid) {
    chan ch = [QUEUE_SIZE - 1] of { int };
    bool result;

    int tmp;

    int rxq;
    int txq;

    // Randomly select a reception queue and a transmission queue.
    atomic {
        rnd(rxq);
        rnd(txq);
    }

    // poll_rx_tx() will be called again if the result is true,
    // which indicates that some packets are processed.
    // https://github.com/tier4/awkernel/blob/53f2cf0579c1392d6f38874da07d58f6d5bd41cb/awkernel_lib/src/net.rs#L571-L573
loop:
    will_poll++;;

    lock(tid, LockRxRingq[rxq]);
    lock(tid, LockTxRingq[txq]);

    lock(tid, LockInner);
    will_poll--;
    interface_poll(ch, tmp, result);
    unlock(tid, LockInner);

    // send packets from the queue.
    net_device_send(ch, tmp);

    unlock(tid, LockTxRingq[txq]);
    unlock(tid, LockRxRingq[rxq]);

    if
        :: result -> goto loop;
        :: else -> skip;
    fi;
}

// Modeling `awkernel_lib::net::if_net::IfNet::poll_tx_only()`.
proctype poll_tx_only(int tid, send_data) {
    chan ch = [QUEUE_SIZE - 1] of { int };
    bool result;
    bool is_full;
    int tmp;

    int txq;
    rnd(txq); // Randomly select a transmission queue.

    IP_Tx ! send_data; // Send an IP packet.

loop:
    // If some task will poll, this task need not to poll.
    atomic {
        if
            :: will_poll > 0 -> goto end;
            :: else -> will_poll++;
        fi;
    }

    lock(tid, LockTxRingq[txq]);

    lock(tid, LockInner);
    will_poll--;
    interface_poll(ch, tmp, result);
    unlock(tid, LockInner);

    is_full = full(ch);

    // send packets from the queue.
    net_device_send(ch, tmp);

    unlock(tid, LockTxRingq[txq]);

    if
        :: is_full -> goto loop;
        :: else -> skip;
    fi;
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
        run poll_rx_tx(tid);
        tid++;
    }

    // Create send tasks.
    for (i: 0 .. NUM_SEND - 1) {
        run poll_tx_only(tid, i);
        tid++;
    }
}

ltl eventually_all_true {
    <> ([] (set[0] && set[1]))
}
