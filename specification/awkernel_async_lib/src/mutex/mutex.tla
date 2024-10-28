----------------- MODULE mutex ----------------
EXTENDS TLC, Integers, Sequences

CONSTANT THREADS

(*--algorithm mutex

variables
    waken = FALSE;
    lock_var = FALSE;
    data = 0;
    wakers = <<>>

define
    eventually_two == <> (data = 2)
end define

procedure lock(thread)
begin
    start_lock:
        if ~lock_var then
            lock_var := TRUE;
            return;
        end if;

    enqueue_thread:
        if Len(wakers) > 0 then
            wakers := Append(wakers, thread);
        else
            goto start_lock;
        end if;

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
        if Len(wakers) > 0 then
            wakers := Tail(wakers);
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
\* BEGIN TRANSLATION (chksum(pcal) = "8f6c2a79" /\ chksum(tla) = "5d9c3255")
\* Process thread at line 52 col 6 changed to thread_
\* Parameter thread of procedure lock at line 18 col 16 changed to thread_l
CONSTANT defaultInitValue
VARIABLES pc, waken, lock_var, data, wakers, stack

(* define statement *)
eventually_two == <> (data = 2)

VARIABLES thread_l, thread

vars == << pc, waken, lock_var, data, wakers, stack, thread_l, thread >>

ProcSet == (THREADS)

Init == (* Global variables *)
        /\ waken = FALSE
        /\ lock_var = FALSE
        /\ data = 0
        /\ wakers = <<>>
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
                          ELSE /\ pc' = [pc EXCEPT ![self] = "enqueue_thread"]
                               /\ UNCHANGED << lock_var, stack, thread_l >>
                    /\ UNCHANGED << waken, data, wakers, thread >>

enqueue_thread(self) == /\ pc[self] = "enqueue_thread"
                        /\ IF Len(wakers) > 0
                              THEN /\ wakers' = Append(wakers, thread_l[self])
                                   /\ pc' = [pc EXCEPT ![self] = "poll_lock"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "start_lock"]
                                   /\ UNCHANGED wakers
                        /\ UNCHANGED << waken, lock_var, data, stack, thread_l, 
                                        thread >>

poll_lock(self) == /\ pc[self] = "poll_lock"
                   /\ waken
                   /\ waken' = FALSE
                   /\ pc' = [pc EXCEPT ![self] = "start_lock"]
                   /\ UNCHANGED << lock_var, data, wakers, stack, thread_l, 
                                   thread >>

lock(self) == start_lock(self) \/ enqueue_thread(self) \/ poll_lock(self)

start_unlock(self) == /\ pc[self] = "start_unlock"
                      /\ Assert((lock_var), 
                                "Failure of assertion at line 42, column 9.")
                      /\ lock_var' = FALSE
                      /\ pc' = [pc EXCEPT ![self] = "wake"]
                      /\ UNCHANGED << waken, data, wakers, stack, thread_l, 
                                      thread >>

wake(self) == /\ pc[self] = "wake"
              /\ IF Len(wakers) > 0
                    THEN /\ wakers' = Tail(wakers)
                         /\ waken' = TRUE
                    ELSE /\ TRUE
                         /\ UNCHANGED << waken, wakers >>
              /\ pc' = [pc EXCEPT ![self] = "Error"]
              /\ UNCHANGED << lock_var, data, stack, thread_l, thread >>

unlock(self) == start_unlock(self) \/ wake(self)

start_thread(self) == /\ pc[self] = "start_thread"
                      /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                                  pc        |->  "add_data",
                                                                  thread_l  |->  thread_l[self] ] >>
                                                              \o stack[self]]
                         /\ thread_l' = [thread_l EXCEPT ![self] = thread[self]]
                      /\ pc' = [pc EXCEPT ![self] = "start_lock"]
                      /\ UNCHANGED << waken, lock_var, data, wakers, thread >>

add_data(self) == /\ pc[self] = "add_data"
                  /\ data' = data + 1
                  /\ pc' = [pc EXCEPT ![self] = "end_thread"]
                  /\ UNCHANGED << waken, lock_var, wakers, stack, thread_l, 
                                  thread >>

end_thread(self) == /\ pc[self] = "end_thread"
                    /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                                pc        |->  "Done",
                                                                thread    |->  thread[self] ] >>
                                                            \o stack[self]]
                       /\ thread' = [thread EXCEPT ![self] = thread[self]]
                    /\ pc' = [pc EXCEPT ![self] = "start_unlock"]
                    /\ UNCHANGED << waken, lock_var, data, wakers, thread_l >>

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
