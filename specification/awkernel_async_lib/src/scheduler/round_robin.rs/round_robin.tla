----------------- MODULE round_robin ----------------
EXTENDS TLC, Integers, Sequences

CONSTANTS TASK_NUM, WORKERS

(*--algorithm round_robin

variables
    \* awkernel_async_lib::scheduler::round_robin::RoundRobinData::queue
    queue = <<>>;

    \* awkernel_async_lib::task::State
    StateInQueue = {};
    StateReady = 1..TASK_NUM;
    StateRunning = {};
    StateWaiting = {};

    result = [x \in 1..TASK_NUM |-> -1]; \* return value of get_next

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
        if task \notin StateInQueue then
            StateWaiting := StateWaiting \ {runnable_task};
            StateInQueue := StateInQueue \union {task};
            queue := Append(queue, task);
        end if;

        return;
end procedure;

\* awkernel_async_lib::scheduler::round_robin::RoundRobinScheduler::get_next()
procedure get_next(pid)
variables
    head;
begin
    start_get_next:
        if Len(queue) = 0 then
            result[pid] := -1;
            return;
        else
            head := Head(queue);
            queue := Tail(queue);
            StateInQueue := StateInQueue \ {head};
            StateRunning := StateRunning \union {head};
            result[pid] := head;
        end if;

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
        if next_task = -1 then
            goto run;
        end if;

    wait_task:
        StateRunning := StateReady \ {next_task};
        StateWaiting := StateWaiting \union  {next_task};

        goto run;
end process;

fair+ process Waker = 1000
variables
    runnable_task;
begin
    start_waker:
        StateWaiting := StateReady;
        StateReady := {};

    wake_task_up:
        await StateWaiting /= {};

        runnable_task := CHOOSE x \in StateWaiting: TRUE;
        call wake_task(runnable_task);

        goto start_waker;
end process;

end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "ab2f7241" /\ chksum(tla) = "1d3d1943")
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

ProcSet == (WORKERS) \cup {1000}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ StateInQueue = {}
        /\ StateReady = 1..TASK_NUM
        /\ StateRunning = {}
        /\ StateWaiting = {}
        /\ result = [x \in 1..TASK_NUM |-> -1]
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
                                        [] self = 1000 -> "start_waker"]

start_wake_task(self) == /\ pc[self] = "start_wake_task"
                         /\ IF task[self] \notin StateInQueue
                               THEN /\ StateWaiting' = StateWaiting \ {runnable_task}
                                    /\ StateInQueue' = (StateInQueue \union {task[self]})
                                    /\ queue' = Append(queue, task[self])
                               ELSE /\ TRUE
                                    /\ UNCHANGED << queue, StateInQueue,
                                                    StateWaiting >>
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << StateReady, StateRunning, result, pid,
                                         head, next_task, runnable_task >>

wake_task(self) == start_wake_task(self)

start_get_next(self) == /\ pc[self] = "start_get_next"
                        /\ IF Len(queue) = 0
                              THEN /\ result' = [result EXCEPT ![pid[self]] = -1]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                                   /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   /\ UNCHANGED << queue, StateInQueue,
                                                   StateRunning >>
                              ELSE /\ head' = [head EXCEPT ![self] = Head(queue)]
                                   /\ queue' = Tail(queue)
                                   /\ StateInQueue' = StateInQueue \ {head'[self]}
                                   /\ StateRunning' = (StateRunning \union {head'[self]})
                                   /\ result' = [result EXCEPT ![pid[self]] = head'[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "end_get_next"]
                                   /\ UNCHANGED << stack, pid >>
                        /\ UNCHANGED << StateReady, StateWaiting, task,
                                        next_task, runnable_task >>

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
                      /\ IF next_task'[self] = -1
                            THEN /\ pc' = [pc EXCEPT ![self] = "run"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "wait_task"]
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

start_waker == /\ pc[1000] = "start_waker"
               /\ StateWaiting' = StateReady
               /\ StateReady' = {}
               /\ pc' = [pc EXCEPT ![1000] = "wake_task_up"]
               /\ UNCHANGED << queue, StateInQueue, StateRunning, result,
                               stack, task, pid, head, next_task,
                               runnable_task >>

wake_task_up == /\ pc[1000] = "wake_task_up"
                /\ StateWaiting /= {}
                /\ runnable_task' = (CHOOSE x \in StateWaiting: TRUE)
                /\ /\ stack' = [stack EXCEPT ![1000] = << [ procedure |->  "wake_task",
                                                            pc        |->  "start_waker",
                                                            task      |->  task[1000] ] >>
                                                        \o stack[1000]]
                   /\ task' = [task EXCEPT ![1000] = runnable_task']
                /\ pc' = [pc EXCEPT ![1000] = "start_wake_task"]
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
        /\ SF_vars(Waker) /\ SF_vars(wake_task(1000))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
