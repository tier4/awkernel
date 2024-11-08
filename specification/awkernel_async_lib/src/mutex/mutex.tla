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
    lock:
        if ~lock_var then
            lock_var := TRUE;
            return;
        else
            wakers := Append(wakers, thread);

            await waken;
            waken := FALSE;
            goto lock;
        end if;
end procedure;

procedure unlock(thread)
begin
    unlock:
        lock_var := FALSE;
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
\* BEGIN TRANSLATION (chksum(pcal) = "f856835c" /\ chksum(tla) = "5579abf5")
\* Label lock of procedure lock at line 21 col 9 changed to lock_
\* Label unlock of procedure unlock at line 36 col 9 changed to unlock_
\* Process thread at line 43 col 6 changed to thread_
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

lock_(self) == /\ pc[self] = "lock_"
               /\ IF ~lock_var
                     THEN /\ lock_var' = TRUE
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ thread_l' = [thread_l EXCEPT ![self] = Head(stack[self]).thread_l]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << waken, wakers >>
                     ELSE /\ wakers' = Append(wakers, thread_l[self])
                          /\ waken
                          /\ waken' = FALSE
                          /\ pc' = [pc EXCEPT ![self] = "lock_"]
                          /\ UNCHANGED << lock_var, stack, thread_l >>
               /\ UNCHANGED << data, thread >>

lock(self) == lock_(self)

unlock_(self) == /\ pc[self] = "unlock_"
                 /\ lock_var' = FALSE
                 /\ IF Len(wakers) > 0
                       THEN /\ wakers' = Tail(wakers)
                            /\ waken' = TRUE
                       ELSE /\ TRUE
                            /\ UNCHANGED << waken, wakers >>
                 /\ pc' = [pc EXCEPT ![self] = "Error"]
                 /\ UNCHANGED << data, stack, thread_l, thread >>

unlock(self) == unlock_(self)

start_thread(self) == /\ pc[self] = "start_thread"
                      /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                                  pc        |->  "add_data",
                                                                  thread_l  |->  thread_l[self] ] >>
                                                              \o stack[self]]
                         /\ thread_l' = [thread_l EXCEPT ![self] = thread[self]]
                      /\ pc' = [pc EXCEPT ![self] = "lock_"]
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
                    /\ pc' = [pc EXCEPT ![self] = "unlock_"]
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
