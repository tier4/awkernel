----------------- MODULE mutex ----------------
EXTENDS TLC, Integers, Sequences

CONSTANT THREADS

(*--algorithm mutex

variables
    waken = FALSE;
    lock_var = FALSE;
    data = 0;
    waiting = FALSE;

define
    eventually_two == <> (data = 2)
end define

procedure lock(thread)
begin
    start_lock:
        if ~lock_var then
            lock_var := TRUE;
            return;
        \* If this else block is used, starvation can be avoided
        \* else
        \*     waiting := TRUE;
        end if;

    \* This causes a starvation
    enqueue_thread:
        waiting := TRUE;

    poll_lock:
        await waken;
        waken := FALSE;
        goto start_lock;
end procedure;

procedure unlock(thread)
begin
    start_unlock:
        assert(lock_var);
        lock_var := FALSE;
    
    wake:
        if waiting then
            waken := TRUE;
        end if;
end procedure;

fair process thread \in THREADS
begin
    start_thread:
        call lock(thread);
    
    add_data:
        data := data + 1;
    
    end_thread:
        call unlock(thread);
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "f67523bd" /\ chksum(tla) = "1c66ce39")
\* Process thread at line 51 col 6 changed to thread_
\* Parameter thread of procedure lock at line 18 col 16 changed to thread_l
CONSTANT defaultInitValue
VARIABLES pc, waken, lock_var, data, waiting, stack

(* define statement *)
eventually_two == <> (data = 2)

VARIABLES thread_l, thread

vars == << pc, waken, lock_var, data, waiting, stack, thread_l, thread >>

ProcSet == (THREADS)

Init == (* Global variables *)
        /\ waken = FALSE
        /\ lock_var = FALSE
        /\ data = 0
        /\ waiting = FALSE
        (* Procedure lock *)
        /\ thread_l = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure unlock *)
        /\ thread = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start_thread"]

start_lock(self) == /\ pc[self] = "start_lock"
                    /\ IF ~lock_var
                          THEN /\ lock_var' = TRUE
                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ thread_l' = [thread_l EXCEPT ![self] = Head(stack[self]).thread_l]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED waiting
                          ELSE /\ waiting' = TRUE
                               /\ pc' = [pc EXCEPT ![self] = "poll_lock"]
                               /\ UNCHANGED << lock_var, stack, thread_l >>
                    /\ UNCHANGED << waken, data, thread >>

poll_lock(self) == /\ pc[self] = "poll_lock"
                   /\ waken
                   /\ waken' = FALSE
                   /\ pc' = [pc EXCEPT ![self] = "start_lock"]
                   /\ UNCHANGED << lock_var, data, waiting, stack, thread_l, 
                                   thread >>

lock(self) == start_lock(self) \/ poll_lock(self)

start_unlock(self) == /\ pc[self] = "start_unlock"
                      /\ Assert((lock_var), 
                                "Failure of assertion at line 42, column 9.")
                      /\ lock_var' = FALSE
                      /\ pc' = [pc EXCEPT ![self] = "wake"]
                      /\ UNCHANGED << waken, data, waiting, stack, thread_l, 
                                      thread >>

wake(self) == /\ pc[self] = "wake"
              /\ IF waiting
                    THEN /\ waken' = TRUE
                    ELSE /\ TRUE
                         /\ waken' = waken
              /\ pc' = [pc EXCEPT ![self] = "Error"]
              /\ UNCHANGED << lock_var, data, waiting, stack, thread_l, thread >>

unlock(self) == start_unlock(self) \/ wake(self)

start_thread(self) == /\ pc[self] = "start_thread"
                      /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                                  pc        |->  "add_data",
                                                                  thread_l  |->  thread_l[self] ] >>
                                                              \o stack[self]]
                         /\ thread_l' = [thread_l EXCEPT ![self] = thread[self]]
                      /\ pc' = [pc EXCEPT ![self] = "start_lock"]
                      /\ UNCHANGED << waken, lock_var, data, waiting, thread >>

add_data(self) == /\ pc[self] = "add_data"
                  /\ data' = data + 1
                  /\ pc' = [pc EXCEPT ![self] = "end_thread"]
                  /\ UNCHANGED << waken, lock_var, waiting, stack, thread_l, 
                                  thread >>

end_thread(self) == /\ pc[self] = "end_thread"
                    /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                                pc        |->  "Done",
                                                                thread    |->  thread[self] ] >>
                                                            \o stack[self]]
                       /\ thread' = [thread EXCEPT ![self] = thread[self]]
                    /\ pc' = [pc EXCEPT ![self] = "start_unlock"]
                    /\ UNCHANGED << waken, lock_var, data, waiting, thread_l >>

thread_(self) == start_thread(self) \/ add_data(self) \/ end_thread(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: lock(self) \/ unlock(self))
           \/ (\E self \in THREADS: thread_(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in THREADS : WF_vars(thread_(self)) /\ WF_vars(lock(self)) /\ WF_vars(unlock(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
