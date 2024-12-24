----------------- MODULE barrier ----------------
EXTENDS TLC, Integers, FiniteSets, Sequences
CONSTANTS Threads, N
ASSUME N \in Nat
ASSUME Threads \in SUBSET Nat

\* It is obvious that a deadlock wil ocuur if this conditon is not satisfied.
ASSUME Cardinality(Threads) % N = 0

(*--algorithm barrier

\* `count` records how many times `wait` has been called.
\* `num_blocked` records the number of blocked threads.
variables 
    count = 0,
    num_blocked = 0,
    blocked = FALSE;

\* If `count` < N, then the thread is blocked. otherwise, all blocked threads are awakened.
\* This property implies that Barrier does not block more than N threads.
define
    BarrierCorrectness == num_blocked = count % N
end define;

\* Note that `wait` is modeled as an atomic operation.
\* Therefore, the implementation needs to use mechanisms such as locks.
procedure wait() begin
    Wait:
        count := count + 1;
        if count % N /= 0 then
            num_blocked := num_blocked + 1;
            blocked := TRUE;
            Await:
                await ~blocked;
            return;
        else
            num_blocked := 0;
            blocked := FALSE;
            return;
        end if;
end procedure;

fair process thread \in Threads begin 
    Body:
        call wait();
end process;

end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "26f45583" /\ chksum(tla) = "34eb2117")
VARIABLES pc, count, num_blocked, blocked, stack

(* define statement *)
BarrierCorrectness == num_blocked = count % N


vars == << pc, count, num_blocked, blocked, stack >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ count = 0
        /\ num_blocked = 0
        /\ blocked = FALSE
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Body"]

Wait(self) == /\ pc[self] = "Wait"
              /\ count' = count + 1
              /\ IF count' % N /= 0
                    THEN /\ num_blocked' = num_blocked + 1
                         /\ blocked' = TRUE
                         /\ pc' = [pc EXCEPT ![self] = "Await"]
                         /\ stack' = stack
                    ELSE /\ num_blocked' = 0
                         /\ blocked' = FALSE
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]

Await(self) == /\ pc[self] = "Await"
               /\ ~blocked
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << count, num_blocked, blocked >>

wait(self) == Wait(self) \/ Await(self)

Body(self) == /\ pc[self] = "Body"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wait",
                                                       pc        |->  "Done" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "Wait"]
              /\ UNCHANGED << count, num_blocked, blocked >>

thread(self) == Body(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: wait(self))
           \/ (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(thread(self)) /\ WF_vars(wait(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
