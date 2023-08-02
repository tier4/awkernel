----------------- MODULE cooperative ----------------
EXTENDS TLC, Integers, Sequences

CONSTANTS TASK_NUM, WORKERS

(*--algorithm cooperative

variables
    \* awkernel_async_lib::scheduler::fifo::FIFOData::queue
    queue = <<>>;

    \* lock variables
    lock_info = [x \in 1..TASK_NUM |-> FALSE];
    lock_future = [x \in 1..TASK_NUM |-> FALSE];
    lock_scheduler = FALSE;

    \* awkernel_async_lib::task::info::in_queue
    in_queue = [x \in 1..TASK_NUM |-> FALSE];

    \* awkernel_async_lib::task::info::need_sched
    need_sched = [x \in 1..TASK_NUM |-> FALSE];

    \* awkernel_async_lib::task::State
    state = [x \in 1..TASK_NUM |-> "Ready"];

    result_next = [x \in WORKERS |-> -1]; \* return value of get_next
    result_future = [x \in WORKERS |-> ""]; \* return value of future

    \* Does a task whose id > TASK_NUM \div 2 wakes another task up?
    wake_other = [x \in ((TASK_NUM \div 2) + 1)..TASK_NUM |-> FALSE];

define
    starvation_free == \A x \in 1..TASK_NUM: (in_queue[x] /\ state[x] /= "Terminated" ~> state[x] = "Running")

    eventually_terminate == <> \A x \in 1..TASK_NUM: (state[x] = "Terminated")
end define

\* awkernel_async_lib::scheduler::fifo::FIFOScheduler::wake_task()
procedure wake_task(task) begin
    start_wake_task:
        await ~lock_scheduler;
        lock_scheduler := TRUE;

    wait_wake_task:
        await ~lock_info[task];
        lock_info[task] := TRUE;

    set_inq_wake_task:
        in_queue[task] := TRUE;
        lock_info[task] := FALSE;

    end_wake_task:
        queue := Append(queue, task);
        lock_scheduler := FALSE;
        return;
end procedure;

\* awkernel_async_lib::task::ArcWake::wake()
procedure wake(task)
begin
    start_wake:
        await ~lock_info[task];
        lock_info[task] := TRUE;

        if state[task] = "Running" \/ state[task] = "ReadyToRun" then
            need_sched_wake:
                need_sched[task] := TRUE;
                lock_info[task] := FALSE;
                return;
        elsif state[task] = "Terminated" then
            wake_but_terminated:
                lock_info[task] := FALSE;
                return;
        end if;

    unlock_wake:
        lock_info[task] := FALSE;

        assert(state[task] = "Ready" \/ state[task] = "Waiting");

    end_wake:
        call wake_task(task);
        return;
end procedure;

\* awkernel_async_lib::scheduler::fifo::FIFOScheduler::get_next()
procedure get_next(pid)
variables
    head;
begin
    start_get_next:
        await ~lock_scheduler;
        lock_scheduler := TRUE;

    check_get_next:
        if queue = <<>> then
            lock_scheduler := FALSE;
            result_next[pid] := -1;
            return;
        end if;

    pop_get_next:
        \* Pop a task from the run queue.
        head := Head(queue);
        queue := Tail(queue);

    wait_get_next:
        await ~lock_info[head];
        lock_info[head] := TRUE;

    end_get_next:
        in_queue[head] := FALSE;

        lock_info[head] := FALSE;
        lock_scheduler := FALSE;

        result_next[pid] := head;
        state[head] := "ReadyToRun";

        return;
end procedure;

\* awkernel_async_lib::task::run_main()
procedure run_main(pid)
variables
    task;
begin
    start_run_main:
        call get_next(pid);

    get_task_run_main:
        task := result_next[pid];

        if task < 0 then
            goto start_run_main;
        end if;

    lock_future_run_main:
        if lock_future[task] then
            call wake(task);
            goto start_run_main;
        else
            lock_future[task] := TRUE;
        end if;

    check_run_main:
        await ~lock_info[task];
        lock_info[task] := TRUE;

    terminated_run_main:
        if state[task] = "Terminated" then
            lock_info[task] := FALSE;
            lock_future[task] := FALSE;
            goto start_run_main;
        end if;

    pre_future_run_main:
        state[task] := "Running";
        lock_info[task] := FALSE;
        need_sched[task] := FALSE;

    start_future_run_main:
        call future(pid, task);

    end_future_run_main:
        lock_future[task] := FALSE;

    post_future_run_main:
        await ~lock_info[task];
        lock_info[task] := TRUE;

        if result_future[pid] = "Pending" then
            state[task] := "Waiting";

            if need_sched[task] then
                sched_future_run_main:
                    need_sched[task] := FALSE;
                    lock_info[task] := FALSE;
                    call wake(task);
                    goto start_run_main;
            end if;
        elsif result_future[pid] = "Ready" then
            state[task] := "Terminated";
        else
            assert(FALSE);
        end if;

    unlock_run_main:
        lock_info[task] := FALSE;

        goto start_run_main;
end procedure;

\* If there is 2 tasks, their task ID's are 1 and 2.
\* This future will execute as follows.
\*
\* step1: Task 2 wakes Task 1 up, and returns "Pending".
\* step2: Task 1 wakes Task 2 up, and returns "Ready".
\* step3: Task 2 returns "Ready".
\*
\* A task will become "Terminated", after returning "Ready".
procedure future(pid, task)
begin
    start_future:
        if task > TASK_NUM \div 2 then
            if wake_other[task] then
                call wake(task); \* to verify eventually_terminate

                set_result_future1: result_future[pid] := "Ready";
            else
                call wake(task - (TASK_NUM \div 2));

                set_result_future2:
                    wake_other[task] := TRUE;
                    result_future[pid] := "Pending";
            end if;
        else
            call wake(task + (TASK_NUM \div 2));
            set_result_future3: result_future[pid] := "Ready";
        end if;

    end_future:
        return;
end procedure;

procedure wake_task_all(task)
begin
    start_wake_task_all:
        if task > TASK_NUM then
            return;
        else
            call wake(task);
            rec_wake_task_all: call wake(task + 1);
        end if;

    end_wake_task_all:
        return;
end procedure;

\* awkernel_async_lib::task::run()
fair+ process W \in WORKERS
begin
    start_worker:
        if self = 1 then
            call wake_task_all(TASK_NUM \div 2 + 1);
        end if;

    run:
        call run_main(self);
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "84d03581" /\ chksum(tla) = "b3893fd1")
\* Procedure variable task of procedure run_main at line 126 col 5 changed to task_
\* Parameter task of procedure wake_task at line 39 col 21 changed to task_w
\* Parameter task of procedure wake at line 59 col 16 changed to task_wa
\* Parameter pid of procedure get_next at line 87 col 20 changed to pid_
\* Parameter pid of procedure run_main at line 124 col 20 changed to pid_r
\* Parameter task of procedure future at line 202 col 23 changed to task_f
CONSTANT defaultInitValue
VARIABLES queue, lock_info, lock_future, lock_scheduler, in_queue, need_sched, 
          state, result_next, result_future, wake_other, pc, stack

(* define statement *)
starvation_free == \A x \in 1..TASK_NUM: (in_queue[x] /\ state[x] /= "Terminated" ~> state[x] = "Running")

eventually_terminate == <> \A x \in 1..TASK_NUM: (state[x] = "Terminated")

VARIABLES task_w, task_wa, pid_, head, pid_r, task_, pid, task_f, task

vars == << queue, lock_info, lock_future, lock_scheduler, in_queue, 
           need_sched, state, result_next, result_future, wake_other, pc, 
           stack, task_w, task_wa, pid_, head, pid_r, task_, pid, task_f, 
           task >>

ProcSet == (WORKERS)

Init == (* Global variables *)
        /\ queue = <<>>
        /\ lock_info = [x \in 1..TASK_NUM |-> FALSE]
        /\ lock_future = [x \in 1..TASK_NUM |-> FALSE]
        /\ lock_scheduler = FALSE
        /\ in_queue = [x \in 1..TASK_NUM |-> FALSE]
        /\ need_sched = [x \in 1..TASK_NUM |-> FALSE]
        /\ state = [x \in 1..TASK_NUM |-> "Ready"]
        /\ result_next = [x \in WORKERS |-> -1]
        /\ result_future = [x \in WORKERS |-> ""]
        /\ wake_other = [x \in ((TASK_NUM \div 2) + 1)..TASK_NUM |-> FALSE]
        (* Procedure wake_task *)
        /\ task_w = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure wake *)
        /\ task_wa = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure get_next *)
        /\ pid_ = [ self \in ProcSet |-> defaultInitValue]
        /\ head = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure run_main *)
        /\ pid_r = [ self \in ProcSet |-> defaultInitValue]
        /\ task_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure future *)
        /\ pid = [ self \in ProcSet |-> defaultInitValue]
        /\ task_f = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure wake_task_all *)
        /\ task = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start_worker"]

start_wake_task(self) == /\ pc[self] = "start_wake_task"
                         /\ ~lock_scheduler
                         /\ lock_scheduler' = TRUE
                         /\ pc' = [pc EXCEPT ![self] = "wait_wake_task"]
                         /\ UNCHANGED << queue, lock_info, lock_future, 
                                         in_queue, need_sched, state, 
                                         result_next, result_future, 
                                         wake_other, stack, task_w, task_wa, 
                                         pid_, head, pid_r, task_, pid, task_f, 
                                         task >>

wait_wake_task(self) == /\ pc[self] = "wait_wake_task"
                        /\ ~lock_info[task_w[self]]
                        /\ lock_info' = [lock_info EXCEPT ![task_w[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = "set_inq_wake_task"]
                        /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                        in_queue, need_sched, state, 
                                        result_next, result_future, wake_other, 
                                        stack, task_w, task_wa, pid_, head, 
                                        pid_r, task_, pid, task_f, task >>

set_inq_wake_task(self) == /\ pc[self] = "set_inq_wake_task"
                           /\ in_queue' = [in_queue EXCEPT ![task_w[self]] = TRUE]
                           /\ lock_info' = [lock_info EXCEPT ![task_w[self]] = FALSE]
                           /\ pc' = [pc EXCEPT ![self] = "end_wake_task"]
                           /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                           need_sched, state, result_next, 
                                           result_future, wake_other, stack, 
                                           task_w, task_wa, pid_, head, pid_r, 
                                           task_, pid, task_f, task >>

end_wake_task(self) == /\ pc[self] = "end_wake_task"
                       /\ queue' = Append(queue, task_w[self])
                       /\ lock_scheduler' = FALSE
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ task_w' = [task_w EXCEPT ![self] = Head(stack[self]).task_w]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << lock_info, lock_future, in_queue, 
                                       need_sched, state, result_next, 
                                       result_future, wake_other, task_wa, 
                                       pid_, head, pid_r, task_, pid, task_f, 
                                       task >>

wake_task(self) == start_wake_task(self) \/ wait_wake_task(self)
                      \/ set_inq_wake_task(self) \/ end_wake_task(self)

start_wake(self) == /\ pc[self] = "start_wake"
                    /\ ~lock_info[task_wa[self]]
                    /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = TRUE]
                    /\ IF state[task_wa[self]] = "Running" \/ state[task_wa[self]] = "ReadyToRun"
                          THEN /\ pc' = [pc EXCEPT ![self] = "need_sched_wake"]
                          ELSE /\ IF state[task_wa[self]] = "Terminated"
                                     THEN /\ pc' = [pc EXCEPT ![self] = "wake_but_terminated"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "unlock_wake"]
                    /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                    in_queue, need_sched, state, result_next, 
                                    result_future, wake_other, stack, task_w, 
                                    task_wa, pid_, head, pid_r, task_, pid, 
                                    task_f, task >>

need_sched_wake(self) == /\ pc[self] = "need_sched_wake"
                         /\ need_sched' = [need_sched EXCEPT ![task_wa[self]] = TRUE]
                         /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = FALSE]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ task_wa' = [task_wa EXCEPT ![self] = Head(stack[self]).task_wa]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                         in_queue, state, result_next, 
                                         result_future, wake_other, task_w, 
                                         pid_, head, pid_r, task_, pid, task_f, 
                                         task >>

wake_but_terminated(self) == /\ pc[self] = "wake_but_terminated"
                             /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ task_wa' = [task_wa EXCEPT ![self] = Head(stack[self]).task_wa]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << queue, lock_future, 
                                             lock_scheduler, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, wake_other, task_w, 
                                             pid_, head, pid_r, task_, pid, 
                                             task_f, task >>

unlock_wake(self) == /\ pc[self] = "unlock_wake"
                     /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = FALSE]
                     /\ Assert((state[task_wa[self]] = "Ready" \/ state[task_wa[self]] = "Waiting"), 
                               "Failure of assertion at line 79, column 9.")
                     /\ pc' = [pc EXCEPT ![self] = "end_wake"]
                     /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                     in_queue, need_sched, state, result_next, 
                                     result_future, wake_other, stack, task_w, 
                                     task_wa, pid_, head, pid_r, task_, pid, 
                                     task_f, task >>

end_wake(self) == /\ pc[self] = "end_wake"
                  /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_task",
                                                              pc        |->  Head(stack[self]).pc,
                                                              task_w    |->  task_w[self] ] >>
                                                          \o Tail(stack[self])]
                     /\ task_w' = [task_w EXCEPT ![self] = task_wa[self]]
                  /\ pc' = [pc EXCEPT ![self] = "start_wake_task"]
                  /\ UNCHANGED << queue, lock_info, lock_future, 
                                  lock_scheduler, in_queue, need_sched, state, 
                                  result_next, result_future, wake_other, 
                                  task_wa, pid_, head, pid_r, task_, pid, 
                                  task_f, task >>

wake(self) == start_wake(self) \/ need_sched_wake(self)
                 \/ wake_but_terminated(self) \/ unlock_wake(self)
                 \/ end_wake(self)

start_get_next(self) == /\ pc[self] = "start_get_next"
                        /\ ~lock_scheduler
                        /\ lock_scheduler' = TRUE
                        /\ pc' = [pc EXCEPT ![self] = "check_get_next"]
                        /\ UNCHANGED << queue, lock_info, lock_future, 
                                        in_queue, need_sched, state, 
                                        result_next, result_future, wake_other, 
                                        stack, task_w, task_wa, pid_, head, 
                                        pid_r, task_, pid, task_f, task >>

check_get_next(self) == /\ pc[self] = "check_get_next"
                        /\ IF queue = <<>>
                              THEN /\ lock_scheduler' = FALSE
                                   /\ result_next' = [result_next EXCEPT ![pid_[self]] = -1]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                                   /\ pid_' = [pid_ EXCEPT ![self] = Head(stack[self]).pid_]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "pop_get_next"]
                                   /\ UNCHANGED << lock_scheduler, result_next, 
                                                   stack, pid_, head >>
                        /\ UNCHANGED << queue, lock_info, lock_future, 
                                        in_queue, need_sched, state, 
                                        result_future, wake_other, task_w, 
                                        task_wa, pid_r, task_, pid, task_f, 
                                        task >>

pop_get_next(self) == /\ pc[self] = "pop_get_next"
                      /\ head' = [head EXCEPT ![self] = Head(queue)]
                      /\ queue' = Tail(queue)
                      /\ pc' = [pc EXCEPT ![self] = "wait_get_next"]
                      /\ UNCHANGED << lock_info, lock_future, lock_scheduler, 
                                      in_queue, need_sched, state, result_next, 
                                      result_future, wake_other, stack, task_w, 
                                      task_wa, pid_, pid_r, task_, pid, task_f, 
                                      task >>

wait_get_next(self) == /\ pc[self] = "wait_get_next"
                       /\ ~lock_info[head[self]]
                       /\ lock_info' = [lock_info EXCEPT ![head[self]] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "end_get_next"]
                       /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                       in_queue, need_sched, state, 
                                       result_next, result_future, wake_other, 
                                       stack, task_w, task_wa, pid_, head, 
                                       pid_r, task_, pid, task_f, task >>

end_get_next(self) == /\ pc[self] = "end_get_next"
                      /\ in_queue' = [in_queue EXCEPT ![head[self]] = FALSE]
                      /\ lock_info' = [lock_info EXCEPT ![head[self]] = FALSE]
                      /\ lock_scheduler' = FALSE
                      /\ result_next' = [result_next EXCEPT ![pid_[self]] = head[self]]
                      /\ state' = [state EXCEPT ![head[self]] = "ReadyToRun"]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                      /\ pid_' = [pid_ EXCEPT ![self] = Head(stack[self]).pid_]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << queue, lock_future, need_sched, 
                                      result_future, wake_other, task_w, 
                                      task_wa, pid_r, task_, pid, task_f, task >>

get_next(self) == start_get_next(self) \/ check_get_next(self)
                     \/ pop_get_next(self) \/ wait_get_next(self)
                     \/ end_get_next(self)

start_run_main(self) == /\ pc[self] = "start_run_main"
                        /\ /\ pid_' = [pid_ EXCEPT ![self] = pid_r[self]]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "get_next",
                                                                    pc        |->  "get_task_run_main",
                                                                    head      |->  head[self],
                                                                    pid_      |->  pid_[self] ] >>
                                                                \o stack[self]]
                        /\ head' = [head EXCEPT ![self] = defaultInitValue]
                        /\ pc' = [pc EXCEPT ![self] = "start_get_next"]
                        /\ UNCHANGED << queue, lock_info, lock_future, 
                                        lock_scheduler, in_queue, need_sched, 
                                        state, result_next, result_future, 
                                        wake_other, task_w, task_wa, pid_r, 
                                        task_, pid, task_f, task >>

get_task_run_main(self) == /\ pc[self] = "get_task_run_main"
                           /\ task_' = [task_ EXCEPT ![self] = result_next[pid_r[self]]]
                           /\ IF task_'[self] < 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "lock_future_run_main"]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, in_queue, 
                                           need_sched, state, result_next, 
                                           result_future, wake_other, stack, 
                                           task_w, task_wa, pid_, head, pid_r, 
                                           pid, task_f, task >>

lock_future_run_main(self) == /\ pc[self] = "lock_future_run_main"
                              /\ IF lock_future[task_[self]]
                                    THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                                     pc        |->  "start_run_main",
                                                                                     task_wa   |->  task_wa[self] ] >>
                                                                                 \o stack[self]]
                                            /\ task_wa' = [task_wa EXCEPT ![self] = task_[self]]
                                         /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                                         /\ UNCHANGED lock_future
                                    ELSE /\ lock_future' = [lock_future EXCEPT ![task_[self]] = TRUE]
                                         /\ pc' = [pc EXCEPT ![self] = "check_run_main"]
                                         /\ UNCHANGED << stack, task_wa >>
                              /\ UNCHANGED << queue, lock_info, lock_scheduler, 
                                              in_queue, need_sched, state, 
                                              result_next, result_future, 
                                              wake_other, task_w, pid_, head, 
                                              pid_r, task_, pid, task_f, task >>

check_run_main(self) == /\ pc[self] = "check_run_main"
                        /\ ~lock_info[task_[self]]
                        /\ lock_info' = [lock_info EXCEPT ![task_[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = "terminated_run_main"]
                        /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                        in_queue, need_sched, state, 
                                        result_next, result_future, wake_other, 
                                        stack, task_w, task_wa, pid_, head, 
                                        pid_r, task_, pid, task_f, task >>

terminated_run_main(self) == /\ pc[self] = "terminated_run_main"
                             /\ IF state[task_[self]] = "Terminated"
                                   THEN /\ lock_info' = [lock_info EXCEPT ![task_[self]] = FALSE]
                                        /\ lock_future' = [lock_future EXCEPT ![task_[self]] = FALSE]
                                        /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "pre_future_run_main"]
                                        /\ UNCHANGED << lock_info, lock_future >>
                             /\ UNCHANGED << queue, lock_scheduler, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, wake_other, stack, 
                                             task_w, task_wa, pid_, head, 
                                             pid_r, task_, pid, task_f, task >>

pre_future_run_main(self) == /\ pc[self] = "pre_future_run_main"
                             /\ state' = [state EXCEPT ![task_[self]] = "Running"]
                             /\ lock_info' = [lock_info EXCEPT ![task_[self]] = FALSE]
                             /\ need_sched' = [need_sched EXCEPT ![task_[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = "start_future_run_main"]
                             /\ UNCHANGED << queue, lock_future, 
                                             lock_scheduler, in_queue, 
                                             result_next, result_future, 
                                             wake_other, stack, task_w, 
                                             task_wa, pid_, head, pid_r, task_, 
                                             pid, task_f, task >>

start_future_run_main(self) == /\ pc[self] = "start_future_run_main"
                               /\ /\ pid' = [pid EXCEPT ![self] = pid_r[self]]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "future",
                                                                           pc        |->  "end_future_run_main",
                                                                           pid       |->  pid[self],
                                                                           task_f    |->  task_f[self] ] >>
                                                                       \o stack[self]]
                                  /\ task_f' = [task_f EXCEPT ![self] = task_[self]]
                               /\ pc' = [pc EXCEPT ![self] = "start_future"]
                               /\ UNCHANGED << queue, lock_info, lock_future, 
                                               lock_scheduler, in_queue, 
                                               need_sched, state, result_next, 
                                               result_future, wake_other, 
                                               task_w, task_wa, pid_, head, 
                                               pid_r, task_, task >>

end_future_run_main(self) == /\ pc[self] = "end_future_run_main"
                             /\ lock_future' = [lock_future EXCEPT ![task_[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = "post_future_run_main"]
                             /\ UNCHANGED << queue, lock_info, lock_scheduler, 
                                             in_queue, need_sched, state, 
                                             result_next, result_future, 
                                             wake_other, stack, task_w, 
                                             task_wa, pid_, head, pid_r, task_, 
                                             pid, task_f, task >>

post_future_run_main(self) == /\ pc[self] = "post_future_run_main"
                              /\ ~lock_info[task_[self]]
                              /\ lock_info' = [lock_info EXCEPT ![task_[self]] = TRUE]
                              /\ IF result_future[pid_r[self]] = "Pending"
                                    THEN /\ state' = [state EXCEPT ![task_[self]] = "Waiting"]
                                         /\ IF need_sched[task_[self]]
                                               THEN /\ pc' = [pc EXCEPT ![self] = "sched_future_run_main"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "unlock_run_main"]
                                    ELSE /\ IF result_future[pid_r[self]] = "Ready"
                                               THEN /\ state' = [state EXCEPT ![task_[self]] = "Terminated"]
                                               ELSE /\ Assert((FALSE), 
                                                              "Failure of assertion at line 185, column 13.")
                                                    /\ state' = state
                                         /\ pc' = [pc EXCEPT ![self] = "unlock_run_main"]
                              /\ UNCHANGED << queue, lock_future, 
                                              lock_scheduler, in_queue, 
                                              need_sched, result_next, 
                                              result_future, wake_other, stack, 
                                              task_w, task_wa, pid_, head, 
                                              pid_r, task_, pid, task_f, task >>

sched_future_run_main(self) == /\ pc[self] = "sched_future_run_main"
                               /\ need_sched' = [need_sched EXCEPT ![task_[self]] = FALSE]
                               /\ lock_info' = [lock_info EXCEPT ![task_[self]] = FALSE]
                               /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                           pc        |->  "start_run_main",
                                                                           task_wa   |->  task_wa[self] ] >>
                                                                       \o stack[self]]
                                  /\ task_wa' = [task_wa EXCEPT ![self] = task_[self]]
                               /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                               /\ UNCHANGED << queue, lock_future, 
                                               lock_scheduler, in_queue, state, 
                                               result_next, result_future, 
                                               wake_other, task_w, pid_, head, 
                                               pid_r, task_, pid, task_f, task >>

unlock_run_main(self) == /\ pc[self] = "unlock_run_main"
                         /\ lock_info' = [lock_info EXCEPT ![task_[self]] = FALSE]
                         /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                         /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                         in_queue, need_sched, state, 
                                         result_next, result_future, 
                                         wake_other, stack, task_w, task_wa, 
                                         pid_, head, pid_r, task_, pid, task_f, 
                                         task >>

run_main(self) == start_run_main(self) \/ get_task_run_main(self)
                     \/ lock_future_run_main(self) \/ check_run_main(self)
                     \/ terminated_run_main(self)
                     \/ pre_future_run_main(self)
                     \/ start_future_run_main(self)
                     \/ end_future_run_main(self)
                     \/ post_future_run_main(self)
                     \/ sched_future_run_main(self)
                     \/ unlock_run_main(self)

start_future(self) == /\ pc[self] = "start_future"
                      /\ IF task_f[self] > TASK_NUM \div 2
                            THEN /\ IF wake_other[task_f[self]]
                                       THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                                        pc        |->  "set_result_future1",
                                                                                        task_wa   |->  task_wa[self] ] >>
                                                                                    \o stack[self]]
                                               /\ task_wa' = [task_wa EXCEPT ![self] = task_f[self]]
                                            /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                                       ELSE /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                                        pc        |->  "set_result_future2",
                                                                                        task_wa   |->  task_wa[self] ] >>
                                                                                    \o stack[self]]
                                               /\ task_wa' = [task_wa EXCEPT ![self] = task_f[self] - (TASK_NUM \div 2)]
                                            /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                            ELSE /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                             pc        |->  "set_result_future3",
                                                                             task_wa   |->  task_wa[self] ] >>
                                                                         \o stack[self]]
                                    /\ task_wa' = [task_wa EXCEPT ![self] = task_f[self] + (TASK_NUM \div 2)]
                                 /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                      /\ UNCHANGED << queue, lock_info, lock_future, 
                                      lock_scheduler, in_queue, need_sched, 
                                      state, result_next, result_future, 
                                      wake_other, task_w, pid_, head, pid_r, 
                                      task_, pid, task_f, task >>

set_result_future3(self) == /\ pc[self] = "set_result_future3"
                            /\ result_future' = [result_future EXCEPT ![pid[self]] = "Ready"]
                            /\ pc' = [pc EXCEPT ![self] = "end_future"]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, in_queue, 
                                            need_sched, state, result_next, 
                                            wake_other, stack, task_w, task_wa, 
                                            pid_, head, pid_r, task_, pid, 
                                            task_f, task >>

set_result_future1(self) == /\ pc[self] = "set_result_future1"
                            /\ result_future' = [result_future EXCEPT ![pid[self]] = "Ready"]
                            /\ pc' = [pc EXCEPT ![self] = "end_future"]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, in_queue, 
                                            need_sched, state, result_next, 
                                            wake_other, stack, task_w, task_wa, 
                                            pid_, head, pid_r, task_, pid, 
                                            task_f, task >>

set_result_future2(self) == /\ pc[self] = "set_result_future2"
                            /\ wake_other' = [wake_other EXCEPT ![task_f[self]] = TRUE]
                            /\ result_future' = [result_future EXCEPT ![pid[self]] = "Pending"]
                            /\ pc' = [pc EXCEPT ![self] = "end_future"]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, in_queue, 
                                            need_sched, state, result_next, 
                                            stack, task_w, task_wa, pid_, head, 
                                            pid_r, task_, pid, task_f, task >>

end_future(self) == /\ pc[self] = "end_future"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                    /\ task_f' = [task_f EXCEPT ![self] = Head(stack[self]).task_f]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << queue, lock_info, lock_future, 
                                    lock_scheduler, in_queue, need_sched, 
                                    state, result_next, result_future, 
                                    wake_other, task_w, task_wa, pid_, head, 
                                    pid_r, task_, task >>

future(self) == start_future(self) \/ set_result_future3(self)
                   \/ set_result_future1(self) \/ set_result_future2(self)
                   \/ end_future(self)

start_wake_task_all(self) == /\ pc[self] = "start_wake_task_all"
                             /\ IF task[self] > TASK_NUM
                                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                        /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                        /\ UNCHANGED task_wa
                                   ELSE /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                                    pc        |->  "rec_wake_task_all",
                                                                                    task_wa   |->  task_wa[self] ] >>
                                                                                \o stack[self]]
                                           /\ task_wa' = [task_wa EXCEPT ![self] = task[self]]
                                        /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                                        /\ task' = task
                             /\ UNCHANGED << queue, lock_info, lock_future, 
                                             lock_scheduler, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, wake_other, task_w, 
                                             pid_, head, pid_r, task_, pid, 
                                             task_f >>

rec_wake_task_all(self) == /\ pc[self] = "rec_wake_task_all"
                           /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                       pc        |->  "end_wake_task_all",
                                                                       task_wa   |->  task_wa[self] ] >>
                                                                   \o stack[self]]
                              /\ task_wa' = [task_wa EXCEPT ![self] = task[self] + 1]
                           /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, in_queue, 
                                           need_sched, state, result_next, 
                                           result_future, wake_other, task_w, 
                                           pid_, head, pid_r, task_, pid, 
                                           task_f, task >>

end_wake_task_all(self) == /\ pc[self] = "end_wake_task_all"
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, in_queue, 
                                           need_sched, state, result_next, 
                                           result_future, wake_other, task_w, 
                                           task_wa, pid_, head, pid_r, task_, 
                                           pid, task_f >>

wake_task_all(self) == start_wake_task_all(self) \/ rec_wake_task_all(self)
                          \/ end_wake_task_all(self)

start_worker(self) == /\ pc[self] = "start_worker"
                      /\ IF self = 1
                            THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_task_all",
                                                                             pc        |->  "run",
                                                                             task      |->  task[self] ] >>
                                                                         \o stack[self]]
                                    /\ task' = [task EXCEPT ![self] = TASK_NUM \div 2 + 1]
                                 /\ pc' = [pc EXCEPT ![self] = "start_wake_task_all"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "run"]
                                 /\ UNCHANGED << stack, task >>
                      /\ UNCHANGED << queue, lock_info, lock_future, 
                                      lock_scheduler, in_queue, need_sched, 
                                      state, result_next, result_future, 
                                      wake_other, task_w, task_wa, pid_, head, 
                                      pid_r, task_, pid, task_f >>

run(self) == /\ pc[self] = "run"
             /\ /\ pid_r' = [pid_r EXCEPT ![self] = self]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "run_main",
                                                         pc        |->  "Done",
                                                         task_     |->  task_[self],
                                                         pid_r     |->  pid_r[self] ] >>
                                                     \o stack[self]]
             /\ task_' = [task_ EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
             /\ UNCHANGED << queue, lock_info, lock_future, lock_scheduler, 
                             in_queue, need_sched, state, result_next, 
                             result_future, wake_other, task_w, task_wa, pid_, 
                             head, pid, task_f, task >>

W(self) == start_worker(self) \/ run(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ wake_task(self) \/ wake(self)
                               \/ get_next(self) \/ run_main(self)
                               \/ future(self) \/ wake_task_all(self))
           \/ (\E self \in WORKERS: W(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in WORKERS : /\ SF_vars(W(self))
                                 /\ SF_vars(wake_task_all(self))
                                 /\ SF_vars(run_main(self))
                                 /\ SF_vars(wake_task(self))
                                 /\ SF_vars(wake(self))
                                 /\ SF_vars(get_next(self))
                                 /\ SF_vars(future(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
