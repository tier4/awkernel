----------------- MODULE cooperative_with_infinite_loop ----------------
EXTENDS TLC, Integers, Sequences

CONSTANTS WORKERS, INFINITE_TASK_NUM, TOTAL_TASK_NUM

(*--algorithm cooperative

variables
    \* awkernel_async_lib::scheduler::fifo::FIFOData::queue
    queue = <<>>;

    \* In the following arrays with [1..TOTAL_TASK_NUM],
    \* [1..INFINITE_TASK_NUM] are for infinite tasks, and
    \* [(INFINITE_TASK_NUM+1)..TOTAL_TASK_NUM] are for finite tasks.

    \* lock variables
    lock_info = [x \in 1..TOTAL_TASK_NUM |-> FALSE];
    lock_future = [x \in 1..TOTAL_TASK_NUM |-> FALSE];
    lock_scheduler = FALSE;

    \* awkernel_async_lib::task::info::need_sched
    need_sched = [x \in 1..TOTAL_TASK_NUM |-> FALSE];

    \* awkernel_async_lib::task::State
    state = [x \in 1..TOTAL_TASK_NUM |-> "Initialized"];

    is_terminated = [x \in 1..TOTAL_TASK_NUM |-> FALSE];

    result_next = [x \in WORKERS |-> -1]; \* return value of get_next
    result_future = [x \in WORKERS |-> ""]; \* return value of future

    \* Has a task already woken?
    woken = [x \in 1..TOTAL_TASK_NUM |-> FALSE];

define
    fair_scheduling == <> \A x \in (INFINITE_TASK_NUM + 1)..TOTAL_TASK_NUM: (state[x] = "Terminated")
end define

\* awkernel_async_lib::scheduler::fifo::FIFOScheduler::wake_task()
procedure wake_task(task) begin
    start_wake_task:
        await ~lock_scheduler;
        lock_scheduler := TRUE;

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

        if state[task] \in {"Running", "Runnable"} then
            need_sched_wake:
                need_sched[task] := TRUE;
                lock_info[task] := FALSE;
                return;
        elsif state[task] = "Terminated" then
            wake_but_terminated:
                lock_info[task] := FALSE;
                return;
        elsif state[task] \in {"Waiting", "Initialized"} then
            state[task] := "Runnable";
        end if;

    unlock_wake:
        lock_info[task] := FALSE;

        assert(state[task] = "Runnable");

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

    is_terminate_get_next:
        if state[head] = "Terminated" then
            lock_info[head] := FALSE;
            goto check_get_next;
        end if;

    end_get_next:
        state[head] := "Running";

        lock_info[head] := FALSE;
        lock_scheduler := FALSE;

        result_next[pid] := head;

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
        lock_info[task] := FALSE;

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

\* Suppose Task 1 and 2 are infinite and finite tasks respectively,
\* This future will execute as follows.
\*
\* step1: Task 1 wakes Task 2 up, and returns "Pending".
\* step2: Task 2 wakes Task 1 up, and returns "Ready".
\* step3: Task 1 returns "Pending" forever.
\*
\* A task will become "Terminated", after returning "Ready".
procedure future(pid, task)
begin
    start_future:
        if task > INFINITE_TASK_NUM then
            call wake(task - INFINITE_TASK_NUM);
            set_result_future1: result_future[pid] := "Ready";
        else
            if woken[task + INFINITE_TASK_NUM] then
                call wake(task);
                set_result_future2: result_future[pid] := "Pending";
            else
                call wake(task + INFINITE_TASK_NUM);
                set_result_future3:
                    woken[task + INFINITE_TASK_NUM] := TRUE;
                    result_future[pid] := "Pending";
            end if;
        end if;

    end_future:
        return;
end procedure;

procedure wake_infinite_tasks(task)
begin
    start_wake_infinite_tasks:
        if task > INFINITE_TASK_NUM then
            return;
        else
            call wake(task);
            rec_wake_infinite_tasks: call wake_infinite_tasks(task + 1);
        end if;

    end_wake_infinite_tasks:
        return;
end procedure;

\* awkernel_async_lib::task::run()
fair+ process W \in WORKERS
begin
    start_worker:
        if self = 1 then
            call wake_infinite_tasks(1);
        end if;

    run:
        call run_main(self);
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "3e173d63" /\ chksum(tla) = "4c52e57d")
\* Procedure variable task of procedure run_main at line 126 col 5 changed to task_
\* Parameter task of procedure wake_task at line 40 col 21 changed to task_w
\* Parameter task of procedure wake at line 52 col 16 changed to task_wa
\* Parameter pid of procedure get_next at line 82 col 20 changed to pid_
\* Parameter pid of procedure run_main at line 124 col 20 changed to pid_r
\* Parameter task of procedure future at line 200 col 23 changed to task_f
CONSTANT defaultInitValue
VARIABLES queue, lock_info, lock_future, lock_scheduler, need_sched, state, 
          is_terminated, result_next, result_future, woken, pc, stack

(* define statement *)
fair_scheduling == <> \A x \in (INFINITE_TASK_NUM + 1)..TOTAL_TASK_NUM: (state[x] = "Terminated")

VARIABLES task_w, task_wa, pid_, head, pid_r, task_, pid, task_f, task

vars == << queue, lock_info, lock_future, lock_scheduler, need_sched, state, 
           is_terminated, result_next, result_future, woken, pc, stack, 
           task_w, task_wa, pid_, head, pid_r, task_, pid, task_f, task >>

ProcSet == (WORKERS)

Init == (* Global variables *)
        /\ queue = <<>>
        /\ lock_info = [x \in 1..TOTAL_TASK_NUM |-> FALSE]
        /\ lock_future = [x \in 1..TOTAL_TASK_NUM |-> FALSE]
        /\ lock_scheduler = FALSE
        /\ need_sched = [x \in 1..TOTAL_TASK_NUM |-> FALSE]
        /\ state = [x \in 1..TOTAL_TASK_NUM |-> "Initialized"]
        /\ is_terminated = [x \in 1..TOTAL_TASK_NUM |-> FALSE]
        /\ result_next = [x \in WORKERS |-> -1]
        /\ result_future = [x \in WORKERS |-> ""]
        /\ woken = [x \in 1..TOTAL_TASK_NUM |-> FALSE]
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
        (* Procedure wake_infinite_tasks *)
        /\ task = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start_worker"]

start_wake_task(self) == /\ pc[self] = "start_wake_task"
                         /\ ~lock_scheduler
                         /\ lock_scheduler' = TRUE
                         /\ pc' = [pc EXCEPT ![self] = "end_wake_task"]
                         /\ UNCHANGED << queue, lock_info, lock_future, 
                                         need_sched, state, is_terminated, 
                                         result_next, result_future, woken, 
                                         stack, task_w, task_wa, pid_, head, 
                                         pid_r, task_, pid, task_f, task >>

end_wake_task(self) == /\ pc[self] = "end_wake_task"
                       /\ queue' = Append(queue, task_w[self])
                       /\ lock_scheduler' = FALSE
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ task_w' = [task_w EXCEPT ![self] = Head(stack[self]).task_w]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << lock_info, lock_future, need_sched, 
                                       state, is_terminated, result_next, 
                                       result_future, woken, task_wa, pid_, 
                                       head, pid_r, task_, pid, task_f, task >>

wake_task(self) == start_wake_task(self) \/ end_wake_task(self)

start_wake(self) == /\ pc[self] = "start_wake"
                    /\ ~lock_info[task_wa[self]]
                    /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = TRUE]
                    /\ IF state[task_wa[self]] \in {"Running", "Runnable"}
                          THEN /\ pc' = [pc EXCEPT ![self] = "need_sched_wake"]
                               /\ state' = state
                          ELSE /\ IF state[task_wa[self]] = "Terminated"
                                     THEN /\ pc' = [pc EXCEPT ![self] = "wake_but_terminated"]
                                          /\ state' = state
                                     ELSE /\ IF state[task_wa[self]] \in {"Waiting", "Initialized"}
                                                THEN /\ state' = [state EXCEPT ![task_wa[self]] = "Runnable"]
                                                ELSE /\ TRUE
                                                     /\ state' = state
                                          /\ pc' = [pc EXCEPT ![self] = "unlock_wake"]
                    /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                    need_sched, is_terminated, result_next, 
                                    result_future, woken, stack, task_w, 
                                    task_wa, pid_, head, pid_r, task_, pid, 
                                    task_f, task >>

need_sched_wake(self) == /\ pc[self] = "need_sched_wake"
                         /\ need_sched' = [need_sched EXCEPT ![task_wa[self]] = TRUE]
                         /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = FALSE]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ task_wa' = [task_wa EXCEPT ![self] = Head(stack[self]).task_wa]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                         state, is_terminated, result_next, 
                                         result_future, woken, task_w, pid_, 
                                         head, pid_r, task_, pid, task_f, task >>

wake_but_terminated(self) == /\ pc[self] = "wake_but_terminated"
                             /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ task_wa' = [task_wa EXCEPT ![self] = Head(stack[self]).task_wa]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << queue, lock_future, 
                                             lock_scheduler, need_sched, state, 
                                             is_terminated, result_next, 
                                             result_future, woken, task_w, 
                                             pid_, head, pid_r, task_, pid, 
                                             task_f, task >>

unlock_wake(self) == /\ pc[self] = "unlock_wake"
                     /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = FALSE]
                     /\ Assert((state[task_wa[self]] = "Runnable"), 
                               "Failure of assertion at line 74, column 9.")
                     /\ pc' = [pc EXCEPT ![self] = "end_wake"]
                     /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                     need_sched, state, is_terminated, 
                                     result_next, result_future, woken, stack, 
                                     task_w, task_wa, pid_, head, pid_r, task_, 
                                     pid, task_f, task >>

end_wake(self) == /\ pc[self] = "end_wake"
                  /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_task",
                                                              pc        |->  Head(stack[self]).pc,
                                                              task_w    |->  task_w[self] ] >>
                                                          \o Tail(stack[self])]
                     /\ task_w' = [task_w EXCEPT ![self] = task_wa[self]]
                  /\ pc' = [pc EXCEPT ![self] = "start_wake_task"]
                  /\ UNCHANGED << queue, lock_info, lock_future, 
                                  lock_scheduler, need_sched, state, 
                                  is_terminated, result_next, result_future, 
                                  woken, task_wa, pid_, head, pid_r, task_, 
                                  pid, task_f, task >>

wake(self) == start_wake(self) \/ need_sched_wake(self)
                 \/ wake_but_terminated(self) \/ unlock_wake(self)
                 \/ end_wake(self)

start_get_next(self) == /\ pc[self] = "start_get_next"
                        /\ ~lock_scheduler
                        /\ lock_scheduler' = TRUE
                        /\ pc' = [pc EXCEPT ![self] = "check_get_next"]
                        /\ UNCHANGED << queue, lock_info, lock_future, 
                                        need_sched, state, is_terminated, 
                                        result_next, result_future, woken, 
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
                                        need_sched, state, is_terminated, 
                                        result_future, woken, task_w, task_wa, 
                                        pid_r, task_, pid, task_f, task >>

pop_get_next(self) == /\ pc[self] = "pop_get_next"
                      /\ head' = [head EXCEPT ![self] = Head(queue)]
                      /\ queue' = Tail(queue)
                      /\ pc' = [pc EXCEPT ![self] = "wait_get_next"]
                      /\ UNCHANGED << lock_info, lock_future, lock_scheduler, 
                                      need_sched, state, is_terminated, 
                                      result_next, result_future, woken, stack, 
                                      task_w, task_wa, pid_, pid_r, task_, pid, 
                                      task_f, task >>

wait_get_next(self) == /\ pc[self] = "wait_get_next"
                       /\ ~lock_info[head[self]]
                       /\ lock_info' = [lock_info EXCEPT ![head[self]] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "is_terminate_get_next"]
                       /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                       need_sched, state, is_terminated, 
                                       result_next, result_future, woken, 
                                       stack, task_w, task_wa, pid_, head, 
                                       pid_r, task_, pid, task_f, task >>

is_terminate_get_next(self) == /\ pc[self] = "is_terminate_get_next"
                               /\ IF state[head[self]] = "Terminated"
                                     THEN /\ lock_info' = [lock_info EXCEPT ![head[self]] = FALSE]
                                          /\ pc' = [pc EXCEPT ![self] = "check_get_next"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "end_get_next"]
                                          /\ UNCHANGED lock_info
                               /\ UNCHANGED << queue, lock_future, 
                                               lock_scheduler, need_sched, 
                                               state, is_terminated, 
                                               result_next, result_future, 
                                               woken, stack, task_w, task_wa, 
                                               pid_, head, pid_r, task_, pid, 
                                               task_f, task >>

end_get_next(self) == /\ pc[self] = "end_get_next"
                      /\ state' = [state EXCEPT ![head[self]] = "Running"]
                      /\ lock_info' = [lock_info EXCEPT ![head[self]] = FALSE]
                      /\ lock_scheduler' = FALSE
                      /\ result_next' = [result_next EXCEPT ![pid_[self]] = head[self]]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                      /\ pid_' = [pid_ EXCEPT ![self] = Head(stack[self]).pid_]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << queue, lock_future, need_sched, 
                                      is_terminated, result_future, woken, 
                                      task_w, task_wa, pid_r, task_, pid, 
                                      task_f, task >>

get_next(self) == start_get_next(self) \/ check_get_next(self)
                     \/ pop_get_next(self) \/ wait_get_next(self)
                     \/ is_terminate_get_next(self) \/ end_get_next(self)

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
                                        lock_scheduler, need_sched, state, 
                                        is_terminated, result_next, 
                                        result_future, woken, task_w, task_wa, 
                                        pid_r, task_, pid, task_f, task >>

get_task_run_main(self) == /\ pc[self] = "get_task_run_main"
                           /\ task_' = [task_ EXCEPT ![self] = result_next[pid_r[self]]]
                           /\ IF task_'[self] < 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "lock_future_run_main"]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, need_sched, state, 
                                           is_terminated, result_next, 
                                           result_future, woken, stack, task_w, 
                                           task_wa, pid_, head, pid_r, pid, 
                                           task_f, task >>

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
                                              need_sched, state, is_terminated, 
                                              result_next, result_future, 
                                              woken, task_w, pid_, head, pid_r, 
                                              task_, pid, task_f, task >>

check_run_main(self) == /\ pc[self] = "check_run_main"
                        /\ ~lock_info[task_[self]]
                        /\ lock_info' = [lock_info EXCEPT ![task_[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = "terminated_run_main"]
                        /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                        need_sched, state, is_terminated, 
                                        result_next, result_future, woken, 
                                        stack, task_w, task_wa, pid_, head, 
                                        pid_r, task_, pid, task_f, task >>

terminated_run_main(self) == /\ pc[self] = "terminated_run_main"
                             /\ IF state[task_[self]] = "Terminated"
                                   THEN /\ lock_info' = [lock_info EXCEPT ![task_[self]] = FALSE]
                                        /\ lock_future' = [lock_future EXCEPT ![task_[self]] = FALSE]
                                        /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "pre_future_run_main"]
                                        /\ UNCHANGED << lock_info, lock_future >>
                             /\ UNCHANGED << queue, lock_scheduler, need_sched, 
                                             state, is_terminated, result_next, 
                                             result_future, woken, stack, 
                                             task_w, task_wa, pid_, head, 
                                             pid_r, task_, pid, task_f, task >>

pre_future_run_main(self) == /\ pc[self] = "pre_future_run_main"
                             /\ lock_info' = [lock_info EXCEPT ![task_[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = "start_future_run_main"]
                             /\ UNCHANGED << queue, lock_future, 
                                             lock_scheduler, need_sched, state, 
                                             is_terminated, result_next, 
                                             result_future, woken, stack, 
                                             task_w, task_wa, pid_, head, 
                                             pid_r, task_, pid, task_f, task >>

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
                                               lock_scheduler, need_sched, 
                                               state, is_terminated, 
                                               result_next, result_future, 
                                               woken, task_w, task_wa, pid_, 
                                               head, pid_r, task_, task >>

end_future_run_main(self) == /\ pc[self] = "end_future_run_main"
                             /\ lock_future' = [lock_future EXCEPT ![task_[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = "post_future_run_main"]
                             /\ UNCHANGED << queue, lock_info, lock_scheduler, 
                                             need_sched, state, is_terminated, 
                                             result_next, result_future, woken, 
                                             stack, task_w, task_wa, pid_, 
                                             head, pid_r, task_, pid, task_f, 
                                             task >>

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
                                                              "Failure of assertion at line 183, column 13.")
                                                    /\ state' = state
                                         /\ pc' = [pc EXCEPT ![self] = "unlock_run_main"]
                              /\ UNCHANGED << queue, lock_future, 
                                              lock_scheduler, need_sched, 
                                              is_terminated, result_next, 
                                              result_future, woken, stack, 
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
                                               lock_scheduler, state, 
                                               is_terminated, result_next, 
                                               result_future, woken, task_w, 
                                               pid_, head, pid_r, task_, pid, 
                                               task_f, task >>

unlock_run_main(self) == /\ pc[self] = "unlock_run_main"
                         /\ lock_info' = [lock_info EXCEPT ![task_[self]] = FALSE]
                         /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                         /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                         need_sched, state, is_terminated, 
                                         result_next, result_future, woken, 
                                         stack, task_w, task_wa, pid_, head, 
                                         pid_r, task_, pid, task_f, task >>

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
                      /\ IF task_f[self] > INFINITE_TASK_NUM
                            THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                             pc        |->  "set_result_future1",
                                                                             task_wa   |->  task_wa[self] ] >>
                                                                         \o stack[self]]
                                    /\ task_wa' = [task_wa EXCEPT ![self] = task_f[self] - INFINITE_TASK_NUM]
                                 /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                            ELSE /\ IF woken[task_f[self] + INFINITE_TASK_NUM]
                                       THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                                        pc        |->  "set_result_future2",
                                                                                        task_wa   |->  task_wa[self] ] >>
                                                                                    \o stack[self]]
                                               /\ task_wa' = [task_wa EXCEPT ![self] = task_f[self]]
                                            /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                                       ELSE /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                                        pc        |->  "set_result_future3",
                                                                                        task_wa   |->  task_wa[self] ] >>
                                                                                    \o stack[self]]
                                               /\ task_wa' = [task_wa EXCEPT ![self] = task_f[self] + INFINITE_TASK_NUM]
                                            /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                      /\ UNCHANGED << queue, lock_info, lock_future, 
                                      lock_scheduler, need_sched, state, 
                                      is_terminated, result_next, 
                                      result_future, woken, task_w, pid_, head, 
                                      pid_r, task_, pid, task_f, task >>

set_result_future1(self) == /\ pc[self] = "set_result_future1"
                            /\ result_future' = [result_future EXCEPT ![pid[self]] = "Ready"]
                            /\ pc' = [pc EXCEPT ![self] = "end_future"]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, need_sched, state, 
                                            is_terminated, result_next, woken, 
                                            stack, task_w, task_wa, pid_, head, 
                                            pid_r, task_, pid, task_f, task >>

set_result_future2(self) == /\ pc[self] = "set_result_future2"
                            /\ result_future' = [result_future EXCEPT ![pid[self]] = "Pending"]
                            /\ pc' = [pc EXCEPT ![self] = "end_future"]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, need_sched, state, 
                                            is_terminated, result_next, woken, 
                                            stack, task_w, task_wa, pid_, head, 
                                            pid_r, task_, pid, task_f, task >>

set_result_future3(self) == /\ pc[self] = "set_result_future3"
                            /\ woken' = [woken EXCEPT ![task_f[self] + INFINITE_TASK_NUM] = TRUE]
                            /\ result_future' = [result_future EXCEPT ![pid[self]] = "Pending"]
                            /\ pc' = [pc EXCEPT ![self] = "end_future"]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, need_sched, state, 
                                            is_terminated, result_next, stack, 
                                            task_w, task_wa, pid_, head, pid_r, 
                                            task_, pid, task_f, task >>

end_future(self) == /\ pc[self] = "end_future"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                    /\ task_f' = [task_f EXCEPT ![self] = Head(stack[self]).task_f]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << queue, lock_info, lock_future, 
                                    lock_scheduler, need_sched, state, 
                                    is_terminated, result_next, result_future, 
                                    woken, task_w, task_wa, pid_, head, pid_r, 
                                    task_, task >>

future(self) == start_future(self) \/ set_result_future1(self)
                   \/ set_result_future2(self) \/ set_result_future3(self)
                   \/ end_future(self)

start_wake_infinite_tasks(self) == /\ pc[self] = "start_wake_infinite_tasks"
                                   /\ IF task[self] > INFINITE_TASK_NUM
                                         THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                              /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                              /\ UNCHANGED task_wa
                                         ELSE /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                                          pc        |->  "rec_wake_infinite_tasks",
                                                                                          task_wa   |->  task_wa[self] ] >>
                                                                                      \o stack[self]]
                                                 /\ task_wa' = [task_wa EXCEPT ![self] = task[self]]
                                              /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                                              /\ task' = task
                                   /\ UNCHANGED << queue, lock_info, 
                                                   lock_future, lock_scheduler, 
                                                   need_sched, state, 
                                                   is_terminated, result_next, 
                                                   result_future, woken, 
                                                   task_w, pid_, head, pid_r, 
                                                   task_, pid, task_f >>

rec_wake_infinite_tasks(self) == /\ pc[self] = "rec_wake_infinite_tasks"
                                 /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_infinite_tasks",
                                                                             pc        |->  "end_wake_infinite_tasks",
                                                                             task      |->  task[self] ] >>
                                                                         \o stack[self]]
                                    /\ task' = [task EXCEPT ![self] = task[self] + 1]
                                 /\ pc' = [pc EXCEPT ![self] = "start_wake_infinite_tasks"]
                                 /\ UNCHANGED << queue, lock_info, lock_future, 
                                                 lock_scheduler, need_sched, 
                                                 state, is_terminated, 
                                                 result_next, result_future, 
                                                 woken, task_w, task_wa, pid_, 
                                                 head, pid_r, task_, pid, 
                                                 task_f >>

end_wake_infinite_tasks(self) == /\ pc[self] = "end_wake_infinite_tasks"
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                 /\ UNCHANGED << queue, lock_info, lock_future, 
                                                 lock_scheduler, need_sched, 
                                                 state, is_terminated, 
                                                 result_next, result_future, 
                                                 woken, task_w, task_wa, pid_, 
                                                 head, pid_r, task_, pid, 
                                                 task_f >>

wake_infinite_tasks(self) == start_wake_infinite_tasks(self)
                                \/ rec_wake_infinite_tasks(self)
                                \/ end_wake_infinite_tasks(self)

start_worker(self) == /\ pc[self] = "start_worker"
                      /\ IF self = 1
                            THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_infinite_tasks",
                                                                             pc        |->  "run",
                                                                             task      |->  task[self] ] >>
                                                                         \o stack[self]]
                                    /\ task' = [task EXCEPT ![self] = 1]
                                 /\ pc' = [pc EXCEPT ![self] = "start_wake_infinite_tasks"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "run"]
                                 /\ UNCHANGED << stack, task >>
                      /\ UNCHANGED << queue, lock_info, lock_future, 
                                      lock_scheduler, need_sched, state, 
                                      is_terminated, result_next, 
                                      result_future, woken, task_w, task_wa, 
                                      pid_, head, pid_r, task_, pid, task_f >>

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
                             need_sched, state, is_terminated, result_next, 
                             result_future, woken, task_w, task_wa, pid_, head, 
                             pid, task_f, task >>

W(self) == start_worker(self) \/ run(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ wake_task(self) \/ wake(self)
                               \/ get_next(self) \/ run_main(self)
                               \/ future(self) \/ wake_infinite_tasks(self))
           \/ (\E self \in WORKERS: W(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in WORKERS : /\ SF_vars(W(self))
                                 /\ SF_vars(wake_infinite_tasks(self))
                                 /\ SF_vars(run_main(self))
                                 /\ SF_vars(wake_task(self))
                                 /\ SF_vars(wake(self))
                                 /\ SF_vars(get_next(self))
                                 /\ SF_vars(future(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
