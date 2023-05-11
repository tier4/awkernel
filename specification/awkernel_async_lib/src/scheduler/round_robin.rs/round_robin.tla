----------------- MODULE round_robin ----------------
EXTENDS TLC, Integers, Sequences

CONSTANTS TASK_NUM, WORKERS

(*--algorithm round_robin

variables
    queue = <<>>;
    StateInQueue = {};
    StateReady = 1..TASK_NUM;
    StateRunning = {};
    StateWaiting = {};

    result = [x \in 1..TASK_NUM |-> <<>>];

define
    starvation_free == \A x \in 1..TASK_NUM:
        (x \in StateInQueue ~> x \in StateRunning)

    in_queue_xor == \A x \in 1..TASK_NUM:
        x \in StateInQueue => x \notin StateReady /\ x \notin StateRunning /\ x \notin StateWaiting

    ready_xor == \A x \in 1..TASK_NUM:
        x \in StateReady => x \notin StateInQueue /\ x \notin StateRunning /\ x \notin StateWaiting

    running_xor == \A x \in 1..TASK_NUM:
        x \in StateRunning => x \notin StateInQueue /\ x \notin StateReady /\ x \notin StateWaiting

    waiting_xor == \A x \in 1..TASK_NUM:
        x \in StateWaiting => x \notin StateInQueue /\ x \notin StateReady /\ x \notin StateRunning
end define

\* awkernel_async_lib::scheduler::round_robin::RoundRobinScheduler::wake_task()
procedure wake_task(task) begin
    start_wake_task:
        if task \in StateInQueue then
            return;
        end if;

    enqueue_wake_task:
        StateWaiting := StateWaiting \ {runnable_task};
        StateInQueue := StateInQueue \union {task};
        queue := Append(queue, task);
        return;
end procedure;

\* awkernel_async_lib::scheduler::round_robin::RoundRobinScheduler::get_next()
procedure get_next(pid)
variables
    head;
begin
    start_get_next:
        head := Head(queue);
        queue := Tail(queue);
        StateInQueue := StateInQueue \ {head};
        StateRunning := StateRunning \union {head};
        result[pid] := head;

    end_get_next:
        return;
end procedure;

\* awkernel_async_lib::task::run()
fair+ process WorkerThread \in WORKERS
variables
    next_task;
begin
    run:
        call get_next(self);

    execute_task:
        next_task := result[self];
        assert next_task \in StateRunning;

    wait_task:
        StateRunning := StateReady \ {next_task};
        StateWaiting := StateWaiting \union  {next_task};

        goto run;
end process;

fair+ process Waker = "Waker"
variables
    runnable_task;
begin
    start_waker:
        StateWaiting := StateReady;
        StateReady := {};

    wake_task_up:
        runnable_task := CHOOSE x \in StateWaiting: TRUE;
        call wake_task(runnable_task);
end process;

end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "c1b154c9" /\ chksum(tla) = "2bf98182")
CONSTANT defaultInitValue
VARIABLES queue, StateInQueue, StateReady, StateRunning, StateWaiting, result, 
          pc, stack

(* define statement *)
starvation_free == \A x \in 1..TASK_NUM:
    (x \in StateInQueue ~> x \in StateRunning)

in_queue_xor == \A x \in 1..TASK_NUM:
    x \in StateInQueue => x \notin StateReady /\ x \notin StateRunning /\ x \notin StateWaiting

ready_xor == \A x \in 1..TASK_NUM:
    x \in StateReady => x \notin StateInQueue /\ x \notin StateRunning /\ x \notin StateWaiting

running_xor == \A x \in 1..TASK_NUM:
    x \in StateRunning => x \notin StateInQueue /\ x \notin StateReady /\ x \notin StateWaiting

waiting_xor == \A x \in 1..TASK_NUM:
    x \in StateWaiting => x \notin StateInQueue /\ x \notin StateReady /\ x \notin StateRunning

VARIABLES task, pid, head, next_task, runnable_task

vars == << queue, StateInQueue, StateReady, StateRunning, StateWaiting, 
           result, pc, stack, task, pid, head, next_task, runnable_task >>

ProcSet == (WORKERS) \cup {"Waker"}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ StateInQueue = {}
        /\ StateReady = 1..TASK_NUM
        /\ StateRunning = {}
        /\ StateWaiting = {}
        /\ result = [x \in 1..TASK_NUM |-> <<>>]
        (* Procedure wake_task *)
        /\ task = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure get_next *)
        /\ pid = [ self \in ProcSet |-> defaultInitValue]
        /\ head = [ self \in ProcSet |-> defaultInitValue]
        (* Process WorkerThread *)
        /\ next_task = [self \in WORKERS |-> defaultInitValue]
        (* Process Waker *)
        /\ runnable_task = defaultInitValue
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in WORKERS -> "run"
                                        [] self = "Waker" -> "start_waker"]

start_wake_task(self) == /\ pc[self] = "start_wake_task"
                         /\ IF task[self] \in StateInQueue
                               THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "enqueue_wake_task"]
                                    /\ UNCHANGED << stack, task >>
                         /\ UNCHANGED << queue, StateInQueue, StateReady, 
                                         StateRunning, StateWaiting, result, 
                                         pid, head, next_task, runnable_task >>

enqueue_wake_task(self) == /\ pc[self] = "enqueue_wake_task"
                           /\ StateWaiting' = StateWaiting \ {runnable_task}
                           /\ StateInQueue' = (StateInQueue \union {task[self]})
                           /\ queue' = Append(queue, task[self])
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << StateReady, StateRunning, result, 
                                           pid, head, next_task, runnable_task >>

wake_task(self) == start_wake_task(self) \/ enqueue_wake_task(self)

start_get_next(self) == /\ pc[self] = "start_get_next"
                        /\ head' = [head EXCEPT ![self] = Head(queue)]
                        /\ queue' = Tail(queue)
                        /\ StateInQueue' = StateInQueue \ {head'[self]}
                        /\ StateRunning' = (StateRunning \union {head'[self]})
                        /\ result' = [result EXCEPT ![pid[self]] = head'[self]]
                        /\ pc' = [pc EXCEPT ![self] = "end_get_next"]
                        /\ UNCHANGED << StateReady, StateWaiting, stack, task, 
                                        pid, next_task, runnable_task >>

end_get_next(self) == /\ pc[self] = "end_get_next"
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                      /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << queue, StateInQueue, StateReady, 
                                      StateRunning, StateWaiting, result, task, 
                                      next_task, runnable_task >>

get_next(self) == start_get_next(self) \/ end_get_next(self)

run(self) == /\ pc[self] = "run"
             /\ /\ pid' = [pid EXCEPT ![self] = self]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "get_next",
                                                         pc        |->  "execute_task",
                                                         head      |->  head[self],
                                                         pid       |->  pid[self] ] >>
                                                     \o stack[self]]
             /\ head' = [head EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "start_get_next"]
             /\ UNCHANGED << queue, StateInQueue, StateReady, StateRunning, 
                             StateWaiting, result, task, next_task, 
                             runnable_task >>

execute_task(self) == /\ pc[self] = "execute_task"
                      /\ next_task' = [next_task EXCEPT ![self] = result[self]]
                      /\ Assert(next_task'[self] \in StateRunning, 
                                "Failure of assertion at line 74, column 9.")
                      /\ pc' = [pc EXCEPT ![self] = "wait_task"]
                      /\ UNCHANGED << queue, StateInQueue, StateReady, 
                                      StateRunning, StateWaiting, result, 
                                      stack, task, pid, head, runnable_task >>

wait_task(self) == /\ pc[self] = "wait_task"
                   /\ StateRunning' = StateReady \ {next_task[self]}
                   /\ StateWaiting' = (StateWaiting \union  {next_task[self]})
                   /\ pc' = [pc EXCEPT ![self] = "run"]
                   /\ UNCHANGED << queue, StateInQueue, StateReady, result, 
                                   stack, task, pid, head, next_task, 
                                   runnable_task >>

WorkerThread(self) == run(self) \/ execute_task(self) \/ wait_task(self)

start_waker == /\ pc["Waker"] = "start_waker"
               /\ StateWaiting' = StateReady
               /\ StateReady' = {}
               /\ pc' = [pc EXCEPT !["Waker"] = "wake_task_up"]
               /\ UNCHANGED << queue, StateInQueue, StateRunning, result, 
                               stack, task, pid, head, next_task, 
                               runnable_task >>

wake_task_up == /\ pc["Waker"] = "wake_task_up"
                /\ runnable_task' = (CHOOSE x \in StateWaiting: TRUE)
                /\ /\ stack' = [stack EXCEPT !["Waker"] = << [ procedure |->  "wake_task",
                                                               pc        |->  "Done",
                                                               task      |->  task["Waker"] ] >>
                                                           \o stack["Waker"]]
                   /\ task' = [task EXCEPT !["Waker"] = runnable_task']
                /\ pc' = [pc EXCEPT !["Waker"] = "start_wake_task"]
                /\ UNCHANGED << queue, StateInQueue, StateReady, StateRunning, 
                                StateWaiting, result, pid, head, next_task >>

Waker == start_waker \/ wake_task_up

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Waker
           \/ (\E self \in ProcSet: wake_task(self) \/ get_next(self))
           \/ (\E self \in WORKERS: WorkerThread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in WORKERS : SF_vars(WorkerThread(self)) /\ SF_vars(get_next(self))
        /\ SF_vars(Waker) /\ SF_vars(wake_task("Waker"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
