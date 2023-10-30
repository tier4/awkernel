----------------- MODULE preemptive ----------------
EXTENDS TLC, Integers, Sequences

CONSTANTS TASK_NUM, FUTURE_TASK, WORKERS, PREEMPTION_NUM

(*--algorithm preemptive

variables
    \* awkernel_async_lib::scheduler::fifo::FIFOData::queue
    queue = <<>>;

    \* lock variables
    lock_info = [x \in 1..TASK_NUM |-> FALSE];
    lock_future = [x \in 1..TASK_NUM |-> FALSE];
    lock_scheduler = FALSE;
    lock_PREEMPTED_TASKS = [x \in WORKERS |-> FALSE];
    lock_NEXT_TASK = [x \in WORKERS |-> FALSE];
    lock_result_context = FALSE;

    \* awkernel_async_lib::task::info::in_queue
    in_queue = [x \in 1..TASK_NUM |-> FALSE];

    \* awkernel_async_lib::task::info::need_sched
    need_sched = [x \in 1..TASK_NUM |-> FALSE];

    \* awkernel_async_lib::task::State
    state = [x \in 1..TASK_NUM |-> "Ready"];

    result_next = [x \in WORKERS |-> -1]; \* return value of get_next
    result_future = [x \in WORKERS |-> ""]; \* return value of future
    result_context = -1; \* return value of take_current_context
    result_thread = [x \in WORKERS |-> -1]; \* return value of take_pooled_thread and create_thread

    \* awkernel_async_lib::task::RUNNING
    RUNNING = [x \in WORKERS |-> -1];

    \* awkernel_async_lib::task::preempt::thread::THREADS
    THREADS_pooled = <<>>;
    THREADS_running = [x \in WORKERS |-> -1];

    \* awkernel_async_lib::task::preempt::THREAD_POOL
    THREAD_POOL = [x \in WORKERS |-> <<>>];

    \* awkernel_async_lib::task::preempt::PREEMPTED_TASKS
    PREEMPTED_TASKS = [x \in WORKERS |-> <<>>];

    \* awkernel_async_lib::task::preempt::NEXT_TASK
    NEXT_TASK = [x \in WORKERS |-> <<>>];

    \* following variables are original ones
    thread_index = 0;
    thread_is_new = [x \in 1..5 |-> FALSE];

    stored_ctx = [x \in WORKERS |-> -1];
    stored_task = [x \in WORKERS |-> -1];

    thread_to_task = [x \in 1..5 |-> -1];
    task_to_thread = [x \in 1..TASK_NUM |-> -1];

    exec_state = [x \in WORKERS |-> "Init"];

    preemption_num = 0;

    wake_other = FALSE;

define
    eventually_terminate == <> \A x \in 1..TASK_NUM: (state[x] = "Terminated")
end define

macro set_preempt_context(task, ctx) begin
    task_to_thread[task] := ctx;
    thread_to_task[ctx] := task;
end macro;

\* awkernel_async_lib::task::preempt::thread::create_thread()
macro create_thread(pid) begin
    thread_index := thread_index + 1;
    result_thread[pid] := thread_index;
    thread_is_new[thread_index] := TRUE;
end macro;

\* awkernel_async_lib::task::preempt::thread::take_current_context()
macro take_current_context(pid) begin
    result_context := THREADS_running[pid];
    THREADS_running[pid] := -1;
end macro;

\* awkernel_async_lib::task::preempt::thread::set_current_context(ctx)
macro set_current_context(pid, ctx) begin
    THREADS_running[pid] := ctx;
end macro;

\* awkernel_async_lib::task::preempt::thread::take_pooled_thread()
macro take_pooled_thread(pid) begin
    if THREADS_pooled = <<>> then
        result_thread[pid] := -1;
    else
        result_thread[pid] := Head(THREADS_pooled);
        THREADS_pooled := Tail(THREADS_pooled);
    end if;
end macro;

\* awkernel_async_lib::task::preempt::thread::make_thread_pooled(thread)
macro make_thread_pooled(thread) begin
    THREADS_pooled := Append(THREADS_pooled, thread);
end macro;

\* awkernel_async_lib::task::preempt::push_to_thread_pool(ctx)
macro push_to_thread_pool(pid, ctx) begin
    THREAD_POOL[pid] := Append(THREAD_POOL[pid], ctx);
end macro;

\* awkernel_async_lib::task::preempt::init()
macro preempt_init(pid) begin
    thread_index := thread_index + 1;
    set_current_context(pid, thread_index);
end macro;

\* awkernel_async_lib::scheduler::fifo::FIFOScheduler::wake_task()
procedure wake_task(task) begin
    start_wake_task:
        await ~lock_scheduler;
        lock_scheduler := TRUE;

    lock_wake_task:
        await ~lock_info[task];
        lock_info[task] := TRUE;

    end_wake_task:
        in_queue[task] := TRUE;
        lock_info[task] := FALSE;
        queue := Append(queue, task);
        lock_scheduler := FALSE;
        return;
end procedure;

\* awkernel_async_lib::task::ArcWake::wake()
procedure wake(task) begin
    start_wake:
        await ~lock_info[task];
        lock_info[task] := TRUE;

        if state[task] = "Running" \/ state[task] = "ReadyToRun" \/ state[task] = "Preempted" then
            need_sched_wake:
                need_sched[task] := TRUE;
                lock_info[task] := FALSE;
                return;
        elsif state[task] = "Terminated" then
            wake_but_terminated:
                lock_info[task] := FALSE;
                return;
        end if;

    end_wake:
        lock_info[task] := FALSE;
        call wake_task(task);
        return;
end procedure;

\* awkernel_async_lib::preempt::get_next_task()
procedure preempt_get_next_task(pid)
variables
    head;
begin
    start_preempt_get_next_task:
        await ~lock_NEXT_TASK[pid];
        lock_NEXT_TASK[pid] := TRUE;

    check_preempt_get_next_task:
        if NEXT_TASK[pid] = <<>> then
            lock_NEXT_TASK[pid] := FALSE;
            result_next[pid] := -1;
            return;
        end if;

    pop_preempt_get_next_task:
        head := Head(NEXT_TASK[pid]);
        NEXT_TASK[pid] := Tail(NEXT_TASK[pid]);

    end_preempt_get_next_task:
        lock_NEXT_TASK[pid] := FALSE;
        result_next[pid] := head;
        return;
end procedure;

\* awkernel_async_lib::scheduler::fifo::FIFOScheduler::get_next()
procedure scheduler_get_next(pid)
variables
    head;
begin
    lock_scheduler_get_next:
        await ~lock_scheduler;
        lock_scheduler := TRUE;

    check_scheduler_get_next:
        if queue = <<>> then
            lock_scheduler := FALSE;
            result_next[pid] := -1;
            return;
        end if;

    pop_scheduler_get_next:
        head := Head(queue);
        queue := Tail(queue);

    wait_scheduler_get_next:
        await ~lock_info[head];
        lock_info[head] := TRUE;

    end_scheduler_get_next:
        in_queue[head] := FALSE;
        state[head] := "ReadyToRun";
        lock_info[head] := FALSE;
        lock_scheduler := FALSE;
        result_next[pid] := head;
        return;
end procedure;

\* awkernel_async_lib::task::get_next_task()
procedure get_next_task(pid) begin
    preempt_get_next_task:
        call preempt_get_next_task(pid);

    scheduler_get_next:
        if result_next[pid] < 0 then
            call scheduler_get_next(pid);
        end if;

    end_get_next_task:
        return;
end procedure;

\* 補助関数
procedure wake_PREEMPTED_TASKS(pid)
variables
    task;
begin
    check_wake_PREEMPTED_TASKS:
        if PREEMPTED_TASKS[pid] = <<>> then
            return;
        end if;

    pop_wake_PREEMPTED_TASKS:
        task := Head(PREEMPTED_TASKS[pid]);
        PREEMPTED_TASKS[pid] := Tail(PREEMPTED_TASKS[pid]);
        call wake_task(task);

    end_wake_PREEMPTED_TASKS:
        call wake_PREEMPTED_TASKS(pid);
        return;
end procedure;

\* 補助関数
procedure make_all_threads_pooled(pid)
variables
    thread;
begin
    check_make_all_threads_pooled:
        if THREAD_POOL[pid] = <<>> then
            return;
        end if;

    pop_make_all_threads_pooled:
        thread := Head(THREAD_POOL[pid]);
        THREAD_POOL[pid] := Tail(THREAD_POOL[pid]);
        make_thread_pooled(thread);

    end_make_all_threads_pooled:
        call make_all_threads_pooled(pid);
        return;
end procedure;

\* awkernel_async_lib::task::preempt::re_schedule()
procedure re_schedule(pid) begin
    lock_preempted_re_schedule:
        await ~lock_PREEMPTED_TASKS[pid];
        lock_PREEMPTED_TASKS[pid] := TRUE;

    wake_re_schedule:
        call wake_PREEMPTED_TASKS(pid);

    unlock_preempted_re_schedule:
        lock_PREEMPTED_TASKS[pid] := FALSE;

    pool_re_schedule:
        call make_all_threads_pooled(pid);

    end_re_schedule:
        return;
end procedure;

\* awkernel_async_lib::task::preempt::thread_entry()
procedure thread_entry(pid, ctx) begin
    start_thread_entry:
        set_current_context(pid, ctx);
        call re_schedule(pid);

    run_main_thread_entry:
        call run_main(pid);
    
    end_thread_entry:
        return;
end procedure;

\* 補助関数
procedure set_exec_state(pid, next_ctx)
begin
    start_set_exec_state:
        THREADS_running[pid] := next_ctx;
        next_task := thread_to_task[next_ctx];
        if next_task > 0 then
            RUNNING[pid] := next_task;
            exec_state[pid] := "Preempted";
        else
            if thread_is_new[next_ctx] = TRUE then
                thread_is_new[next_ctx] := FALSE;
                call thread_entry(pid, next_ctx);
            else
                exec_state[pid] := "Yielded";
            end if;
        end if;

    end_set_exec_state:
        return;
end procedure;

\* awkernel_async_lib::task::preempt::yield_and_pool()
procedure yield_and_pool(pid, next_ctx)
variables
    current_ctx;
begin
    start_yield_and_pool:
        if exec_state[pid] = "Init" then
            goto lock_result_yield_and_pool;
        elsif exec_state[pid] = "Yielded" then
            exec_state[pid] := "Init";
            current_ctx := stored_ctx[pid];
            goto re_schedule_yield_and_pool;
        end if;

    lock_result_yield_and_pool:
        await ~lock_result_context;
        lock_result_context := TRUE;
        take_current_context(pid);

    unlock_result_yield_and_pool:
        current_ctx := result_context;
        lock_result_context := FALSE;
        push_to_thread_pool(pid, current_ctx);

    \* context_switch
    context_switch_yield_and_pool:
        stored_task[pid] := thread_to_task[next_ctx];
        stored_ctx[pid] := next_ctx;
        call set_exec_state(pid, next_ctx);
        return;

    re_schedule_yield_and_pool:
        set_current_context(pid, current_ctx);
        call re_schedule(pid);

    end_yield_and_pool:
        return;
end procedure;

\* awkernel_async_lib::task::preempt::yield_preempted_and_wake_task()
procedure yield_preempted_and_wake_task(pid, task, next_thread)
variables
    current_ctx;
begin
    start_yield_preempted_and_wake_task:
        if exec_state[pid] = "Init" then
            goto lock_result_yield_preempted_and_wake_task;
        elsif exec_state[pid] = "Preempted" then
            exec_state[pid] := "Init";
            current_ctx := stored_ctx[pid];
            task := stored_task;
            goto re_schedule_yield_preempted_and_wake_task;
        end if;

    lock_result_yield_preempted_and_wake_task:
        await ~lock_result_context;
        lock_result_context := TRUE;
        take_current_context(pid);

    unlock_result_yield_preempted_and_wake_task:
        current_ctx := result_context;
        lock_result_context := FALSE;

    lock_task_yield_preempted_and_wake_task:
        await ~lock_info[task];
        lock_info[task] := TRUE;

    set_preempted_yield_preempted_and_wake_task:
        set_preempt_context(task, current_ctx);

    set_state_yield_preempted_and_wake_task:
        state[task] := "Preempted";
        lock_info[task] := FALSE;

    lock_preempted_yield_preempted_and_wake_task:
        await ~lock_PREEMPTED_TASKS[pid];
        lock_PREEMPTED_TASKS[pid] := TRUE;

    push_task_yield_preempted_and_wake_task:
        PREEMPTED_TASKS[pid] := <<task>> \o PREEMPTED_TASKS[pid];
        lock_PREEMPTED_TASKS[pid] := FALSE;

    \* context_switch
    context_switch_yield_preempted_and_wake_task:
        stored_task[pid] := thread_to_task[next_thread];
        stored_ctx[pid] := next_thread;
        call set_exec_state(pid, next_thread);
        return;

    re_schedule_yield_preempted_and_wake_task:
        set_current_context(pid, current_ctx);
        call re_schedule(pid);

    end_yield_preempted_and_wake_task:
        return;
end procedure;

\* awkernel_async_lib::task::run_main()
procedure run_main(pid)
variables
    task,
    next_ctx
begin
    start_run_main:
        if exec_state[pid] = "Init" then
            goto get_next_run_main;
        elsif exec_state[pid] = "Yielded" then
            task := stored_task[pid];
            next_ctx := stored_ctx[pid];
            goto yield_run_main;
        elsif exec_state[pid] = "Preempted" then
            task := stored_task[pid];
            goto preempt_after_run_main;
        elsif exec_state[pid] = "NotFound" then
            exec_state[pid] := "Init";
            goto lock_future2_run_main;
        end if;

    get_next_run_main:
        call get_next_task(pid);

    get_task_run_main:
        task := result_next[pid];
        if task < 0 then
            return_run_main:
                return;
            \* goto start_run_main;
        end if;

    lock_task_run_main:
        next_ctx := task_to_thread[task];

        if next_ctx > 0 then
            state[task] := "Running";

            yield_run_main:
                call yield_and_pool(pid, next_ctx);

            continue_run_main:
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
        need_sched[task] := FALSE;
        lock_info[task] := FALSE;

    set_task_run_main:
        RUNNING[pid] := task;
        lock_future[task] := FALSE;

    preempt_run_main:
        if preemption_num < PREEMPTION_NUM then
            preemption_num := preemption_num + 1;
            call do_preemption(pid);

            continue_run_main3:
                goto start_run_main;

            preempt_after_run_main:
                call do_preemption(pid);
        end if;

    lock_future2_run_main:
        lock_future[task] := TRUE;

    start_future_run_main:
        call future(pid, task);

    end_future_run_main:
        lock_future[task] := FALSE;

    unset_task_run_main:
        RUNNING[pid] := -1;

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

    continue_run_main2:
        lock_info[task] := FALSE;
        goto start_run_main;
end procedure;

\* procedure future(pid, task) begin
\*     start_future:
\*         result_future[pid] := "Ready";
\*         return;
\* end procedure;

\* 1. Task 'FUTURE_TASK - 1' wakes 'FUTURE_TASK' and returns Pending
\* 2. Task 'FUTURE_TASK' wakes 'FUTURE_TASK - 1' and returns Ready
\* 3. Task 'FUTURE_TASK - 1' returns Ready
procedure future(pid, task)
begin
    start_future:
        if task = FUTURE_TASK - 1 then
            if wake_other then
                result_future[pid] := "Ready";
                call wake(task);
            else
                wake_other := TRUE;
                result_future[pid] := "Pending";
                call wake(FUTURE_TASK);
            end if;
        elsif task = FUTURE_TASK then
            result_future[pid] := "Ready";
            call wake(FUTURE_TASK - 1);
        else
            result_future[pid] := "Ready";
        end if;

    end_future:
        return;
end procedure;

\* awkernel_async_lib::task::preempt::do_preemption()
procedure do_preemption(pid)
variables
    current_task,
    next_task,
    next_thread;
begin
    start_do_preemption:
        if exec_state[pid] = "Init" then
            goto get_current_task_do_preemption;
        elsif exec_state[pid] = "Preempted" then
            current_task := stored_task[pid];
            next_thread := stored_ctx[pid];
            goto end_do_preemption;
        end if;

    get_current_task_do_preemption:
        current_task := RUNNING[pid];
        if current_task < 0 then
            exec_state[pid] := "NotFound";
            exit_do_preemption1: return;
        end if;

    get_next_task_do_preemption:
        call get_next_task(pid);

    set_task_do_preemption:
        next_task := result_next[pid];
        if next_task < 0 then
            exec_state[pid] := "NotFound";
            exit_do_preemption2: return;
        end if;

    lock_task_do_preemption:
        await ~lock_info[next_task];
        lock_info[next_task] := TRUE;
        next_thread := task_to_thread[next_task];

    yield_do_preemption:
        if next_thread > 0 then
            call yield_preempted_and_wake_task(pid, current_task, next_thread);

            exit_do_preemption3:
                lock_info[next_task] := FALSE;
                return;
        end if;

    unlock_task_do_preemption:
        lock_info[next_task] := FALSE;
        take_pooled_thread(pid);

    get_thread_do_preemption:
        if result_thread[pid] < 0 then
            create_thread(pid);
        end if;

    set_thread_do_preemption:
        next_thread := result_thread[pid];

    wait_NEXT_TASK_do_preemption:
        await ~lock_NEXT_TASK[pid];
        lock_NEXT_TASK[pid] := TRUE;

    push_NEXT_TASK_do_preemption:
        NEXT_TASK[pid] := Append(NEXT_TASK[pid], next_task);
        lock_NEXT_TASK[pid] := FALSE;

    end_do_preemption:
        call yield_preempted_and_wake_task(pid, current_task, next_thread);
        exit_do_preemption4: return;
end procedure;

procedure wake_task_all(task) begin
    start_wake_task_all:
        if task > TASK_NUM - 1 then
            return;
        else
            call wake(task);
            rec_wake_task_all: call wake_task_all(task + 1);
        end if;

    end_wake_task_all:
        return;
end procedure;

\* awkernel_async_lib::task::run()
fair process W \in WORKERS begin
    start_worker:
        if self = 1 then
            call wake_task_all(self);
        end if;

    preempt_init:
        preempt_init(self);

    run:
        call run_main(self);
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "6178ebae" /\ chksum(tla) = "e7ed6079")
\* Label preempt_get_next_task of procedure get_next_task at line 222 col 9 changed to preempt_get_next_task_
\* Label scheduler_get_next of procedure get_next_task at line 225 col 9 changed to scheduler_get_next_
\* Procedure variable head of procedure preempt_get_next_task at line 163 col 5 changed to head_
\* Procedure variable task of procedure wake_PREEMPTED_TASKS at line 236 col 5 changed to task_
\* Procedure variable current_ctx of procedure yield_and_pool at line 330 col 5 changed to current_ctx_
\* Procedure variable task of procedure run_main at line 427 col 5 changed to task_r
\* Procedure variable next_ctx of procedure run_main at line 428 col 5 changed to next_ctx_
\* Procedure variable next_thread of procedure do_preemption at line 583 col 5 changed to next_thread_
\* Parameter task of procedure wake_task at line 120 col 21 changed to task_w
\* Parameter task of procedure wake at line 138 col 16 changed to task_wa
\* Parameter pid of procedure preempt_get_next_task at line 161 col 33 changed to pid_
\* Parameter pid of procedure scheduler_get_next at line 187 col 30 changed to pid_s
\* Parameter pid of procedure get_next_task at line 220 col 25 changed to pid_g
\* Parameter pid of procedure wake_PREEMPTED_TASKS at line 234 col 32 changed to pid_w
\* Parameter pid of procedure make_all_threads_pooled at line 254 col 35 changed to pid_m
\* Parameter pid of procedure re_schedule at line 274 col 23 changed to pid_r
\* Parameter pid of procedure thread_entry at line 293 col 24 changed to pid_t
\* Parameter pid of procedure set_exec_state at line 306 col 26 changed to pid_se
\* Parameter next_ctx of procedure set_exec_state at line 306 col 31 changed to next_ctx_s
\* Parameter pid of procedure yield_and_pool at line 328 col 26 changed to pid_y
\* Parameter pid of procedure yield_preempted_and_wake_task at line 367 col 41 changed to pid_yi
\* Parameter task of procedure yield_preempted_and_wake_task at line 367 col 46 changed to task_y
\* Parameter pid of procedure run_main at line 425 col 20 changed to pid_ru
\* Parameter pid of procedure future at line 555 col 18 changed to pid_f
\* Parameter task of procedure future at line 555 col 23 changed to task_f
CONSTANT defaultInitValue
VARIABLES queue, lock_info, lock_future, lock_scheduler, lock_PREEMPTED_TASKS, 
          lock_NEXT_TASK, lock_result_context, in_queue, need_sched, state, 
          result_next, result_future, result_context, result_thread, RUNNING, 
          THREADS_pooled, THREADS_running, THREAD_POOL, PREEMPTED_TASKS, 
          NEXT_TASK, thread_index, thread_is_new, stored_ctx, stored_task, 
          thread_to_task, task_to_thread, exec_state, preemption_num, 
          wake_other, pc, stack

(* define statement *)
eventually_terminate == <> \A x \in 1..TASK_NUM: (state[x] = "Terminated")

VARIABLES task_w, task_wa, pid_, head_, pid_s, head, pid_g, pid_w, task_, 
          pid_m, thread, pid_r, pid_t, ctx, pid_se, next_ctx_s, pid_y, 
          next_ctx, current_ctx_, pid_yi, task_y, next_thread, current_ctx, 
          pid_ru, task_r, next_ctx_, pid_f, task_f, pid, current_task, 
          next_task, next_thread_, task

vars == << queue, lock_info, lock_future, lock_scheduler, 
           lock_PREEMPTED_TASKS, lock_NEXT_TASK, lock_result_context, 
           in_queue, need_sched, state, result_next, result_future, 
           result_context, result_thread, RUNNING, THREADS_pooled, 
           THREADS_running, THREAD_POOL, PREEMPTED_TASKS, NEXT_TASK, 
           thread_index, thread_is_new, stored_ctx, stored_task, 
           thread_to_task, task_to_thread, exec_state, preemption_num, 
           wake_other, pc, stack, task_w, task_wa, pid_, head_, pid_s, head, 
           pid_g, pid_w, task_, pid_m, thread, pid_r, pid_t, ctx, pid_se, 
           next_ctx_s, pid_y, next_ctx, current_ctx_, pid_yi, task_y, 
           next_thread, current_ctx, pid_ru, task_r, next_ctx_, pid_f, task_f, 
           pid, current_task, next_task, next_thread_, task >>

ProcSet == (WORKERS)

Init == (* Global variables *)
        /\ queue = <<>>
        /\ lock_info = [x \in 1..TASK_NUM |-> FALSE]
        /\ lock_future = [x \in 1..TASK_NUM |-> FALSE]
        /\ lock_scheduler = FALSE
        /\ lock_PREEMPTED_TASKS = [x \in WORKERS |-> FALSE]
        /\ lock_NEXT_TASK = [x \in WORKERS |-> FALSE]
        /\ lock_result_context = FALSE
        /\ in_queue = [x \in 1..TASK_NUM |-> FALSE]
        /\ need_sched = [x \in 1..TASK_NUM |-> FALSE]
        /\ state = [x \in 1..TASK_NUM |-> "Ready"]
        /\ result_next = [x \in WORKERS |-> -1]
        /\ result_future = [x \in WORKERS |-> ""]
        /\ result_context = -1
        /\ result_thread = [x \in WORKERS |-> -1]
        /\ RUNNING = [x \in WORKERS |-> -1]
        /\ THREADS_pooled = <<>>
        /\ THREADS_running = [x \in WORKERS |-> -1]
        /\ THREAD_POOL = [x \in WORKERS |-> <<>>]
        /\ PREEMPTED_TASKS = [x \in WORKERS |-> <<>>]
        /\ NEXT_TASK = [x \in WORKERS |-> <<>>]
        /\ thread_index = 0
        /\ thread_is_new = [x \in 1..5 |-> FALSE]
        /\ stored_ctx = [x \in WORKERS |-> -1]
        /\ stored_task = [x \in WORKERS |-> -1]
        /\ thread_to_task = [x \in 1..5 |-> -1]
        /\ task_to_thread = [x \in 1..TASK_NUM |-> -1]
        /\ exec_state = [x \in WORKERS |-> "Init"]
        /\ preemption_num = 0
        /\ wake_other = FALSE
        (* Procedure wake_task *)
        /\ task_w = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure wake *)
        /\ task_wa = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure preempt_get_next_task *)
        /\ pid_ = [ self \in ProcSet |-> defaultInitValue]
        /\ head_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure scheduler_get_next *)
        /\ pid_s = [ self \in ProcSet |-> defaultInitValue]
        /\ head = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure get_next_task *)
        /\ pid_g = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure wake_PREEMPTED_TASKS *)
        /\ pid_w = [ self \in ProcSet |-> defaultInitValue]
        /\ task_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure make_all_threads_pooled *)
        /\ pid_m = [ self \in ProcSet |-> defaultInitValue]
        /\ thread = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure re_schedule *)
        /\ pid_r = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure thread_entry *)
        /\ pid_t = [ self \in ProcSet |-> defaultInitValue]
        /\ ctx = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure set_exec_state *)
        /\ pid_se = [ self \in ProcSet |-> defaultInitValue]
        /\ next_ctx_s = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure yield_and_pool *)
        /\ pid_y = [ self \in ProcSet |-> defaultInitValue]
        /\ next_ctx = [ self \in ProcSet |-> defaultInitValue]
        /\ current_ctx_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure yield_preempted_and_wake_task *)
        /\ pid_yi = [ self \in ProcSet |-> defaultInitValue]
        /\ task_y = [ self \in ProcSet |-> defaultInitValue]
        /\ next_thread = [ self \in ProcSet |-> defaultInitValue]
        /\ current_ctx = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure run_main *)
        /\ pid_ru = [ self \in ProcSet |-> defaultInitValue]
        /\ task_r = [ self \in ProcSet |-> defaultInitValue]
        /\ next_ctx_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure future *)
        /\ pid_f = [ self \in ProcSet |-> defaultInitValue]
        /\ task_f = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure do_preemption *)
        /\ pid = [ self \in ProcSet |-> defaultInitValue]
        /\ current_task = [ self \in ProcSet |-> defaultInitValue]
        /\ next_task = [ self \in ProcSet |-> defaultInitValue]
        /\ next_thread_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure wake_task_all *)
        /\ task = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start_worker"]

start_wake_task(self) == /\ pc[self] = "start_wake_task"
                         /\ ~lock_scheduler
                         /\ lock_scheduler' = TRUE
                         /\ pc' = [pc EXCEPT ![self] = "lock_wake_task"]
                         /\ UNCHANGED << queue, lock_info, lock_future, 
                                         lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                         lock_result_context, in_queue, 
                                         need_sched, state, result_next, 
                                         result_future, result_context, 
                                         result_thread, RUNNING, 
                                         THREADS_pooled, THREADS_running, 
                                         THREAD_POOL, PREEMPTED_TASKS, 
                                         NEXT_TASK, thread_index, 
                                         thread_is_new, stored_ctx, 
                                         stored_task, thread_to_task, 
                                         task_to_thread, exec_state, 
                                         preemption_num, wake_other, stack, 
                                         task_w, task_wa, pid_, head_, pid_s, 
                                         head, pid_g, pid_w, task_, pid_m, 
                                         thread, pid_r, pid_t, ctx, pid_se, 
                                         next_ctx_s, pid_y, next_ctx, 
                                         current_ctx_, pid_yi, task_y, 
                                         next_thread, current_ctx, pid_ru, 
                                         task_r, next_ctx_, pid_f, task_f, pid, 
                                         current_task, next_task, next_thread_, 
                                         task >>

lock_wake_task(self) == /\ pc[self] = "lock_wake_task"
                        /\ ~lock_info[task_w[self]]
                        /\ lock_info' = [lock_info EXCEPT ![task_w[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = "end_wake_task"]
                        /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                        lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                        lock_result_context, in_queue, 
                                        need_sched, state, result_next, 
                                        result_future, result_context, 
                                        result_thread, RUNNING, THREADS_pooled, 
                                        THREADS_running, THREAD_POOL, 
                                        PREEMPTED_TASKS, NEXT_TASK, 
                                        thread_index, thread_is_new, 
                                        stored_ctx, stored_task, 
                                        thread_to_task, task_to_thread, 
                                        exec_state, preemption_num, wake_other, 
                                        stack, task_w, task_wa, pid_, head_, 
                                        pid_s, head, pid_g, pid_w, task_, 
                                        pid_m, thread, pid_r, pid_t, ctx, 
                                        pid_se, next_ctx_s, pid_y, next_ctx, 
                                        current_ctx_, pid_yi, task_y, 
                                        next_thread, current_ctx, pid_ru, 
                                        task_r, next_ctx_, pid_f, task_f, pid, 
                                        current_task, next_task, next_thread_, 
                                        task >>

end_wake_task(self) == /\ pc[self] = "end_wake_task"
                       /\ in_queue' = [in_queue EXCEPT ![task_w[self]] = TRUE]
                       /\ lock_info' = [lock_info EXCEPT ![task_w[self]] = FALSE]
                       /\ queue' = Append(queue, task_w[self])
                       /\ lock_scheduler' = FALSE
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ task_w' = [task_w EXCEPT ![self] = Head(stack[self]).task_w]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << lock_future, lock_PREEMPTED_TASKS, 
                                       lock_NEXT_TASK, lock_result_context, 
                                       need_sched, state, result_next, 
                                       result_future, result_context, 
                                       result_thread, RUNNING, THREADS_pooled, 
                                       THREADS_running, THREAD_POOL, 
                                       PREEMPTED_TASKS, NEXT_TASK, 
                                       thread_index, thread_is_new, stored_ctx, 
                                       stored_task, thread_to_task, 
                                       task_to_thread, exec_state, 
                                       preemption_num, wake_other, task_wa, 
                                       pid_, head_, pid_s, head, pid_g, pid_w, 
                                       task_, pid_m, thread, pid_r, pid_t, ctx, 
                                       pid_se, next_ctx_s, pid_y, next_ctx, 
                                       current_ctx_, pid_yi, task_y, 
                                       next_thread, current_ctx, pid_ru, 
                                       task_r, next_ctx_, pid_f, task_f, pid, 
                                       current_task, next_task, next_thread_, 
                                       task >>

wake_task(self) == start_wake_task(self) \/ lock_wake_task(self)
                      \/ end_wake_task(self)

start_wake(self) == /\ pc[self] = "start_wake"
                    /\ ~lock_info[task_wa[self]]
                    /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = TRUE]
                    /\ IF state[task_wa[self]] = "Running" \/ state[task_wa[self]] = "ReadyToRun" \/ state[task_wa[self]] = "Preempted"
                          THEN /\ pc' = [pc EXCEPT ![self] = "need_sched_wake"]
                          ELSE /\ IF state[task_wa[self]] = "Terminated"
                                     THEN /\ pc' = [pc EXCEPT ![self] = "wake_but_terminated"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "end_wake"]
                    /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                    lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                    lock_result_context, in_queue, need_sched, 
                                    state, result_next, result_future, 
                                    result_context, result_thread, RUNNING, 
                                    THREADS_pooled, THREADS_running, 
                                    THREAD_POOL, PREEMPTED_TASKS, NEXT_TASK, 
                                    thread_index, thread_is_new, stored_ctx, 
                                    stored_task, thread_to_task, 
                                    task_to_thread, exec_state, preemption_num, 
                                    wake_other, stack, task_w, task_wa, pid_, 
                                    head_, pid_s, head, pid_g, pid_w, task_, 
                                    pid_m, thread, pid_r, pid_t, ctx, pid_se, 
                                    next_ctx_s, pid_y, next_ctx, current_ctx_, 
                                    pid_yi, task_y, next_thread, current_ctx, 
                                    pid_ru, task_r, next_ctx_, pid_f, task_f, 
                                    pid, current_task, next_task, next_thread_, 
                                    task >>

need_sched_wake(self) == /\ pc[self] = "need_sched_wake"
                         /\ need_sched' = [need_sched EXCEPT ![task_wa[self]] = TRUE]
                         /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = FALSE]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ task_wa' = [task_wa EXCEPT ![self] = Head(stack[self]).task_wa]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                         lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                         lock_result_context, in_queue, state, 
                                         result_next, result_future, 
                                         result_context, result_thread, 
                                         RUNNING, THREADS_pooled, 
                                         THREADS_running, THREAD_POOL, 
                                         PREEMPTED_TASKS, NEXT_TASK, 
                                         thread_index, thread_is_new, 
                                         stored_ctx, stored_task, 
                                         thread_to_task, task_to_thread, 
                                         exec_state, preemption_num, 
                                         wake_other, task_w, pid_, head_, 
                                         pid_s, head, pid_g, pid_w, task_, 
                                         pid_m, thread, pid_r, pid_t, ctx, 
                                         pid_se, next_ctx_s, pid_y, next_ctx, 
                                         current_ctx_, pid_yi, task_y, 
                                         next_thread, current_ctx, pid_ru, 
                                         task_r, next_ctx_, pid_f, task_f, pid, 
                                         current_task, next_task, next_thread_, 
                                         task >>

wake_but_terminated(self) == /\ pc[self] = "wake_but_terminated"
                             /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ task_wa' = [task_wa EXCEPT ![self] = Head(stack[self]).task_wa]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << queue, lock_future, 
                                             lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             thread_is_new, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             preemption_num, wake_other, 
                                             task_w, pid_, head_, pid_s, head, 
                                             pid_g, pid_w, task_, pid_m, 
                                             thread, pid_r, pid_t, ctx, pid_se, 
                                             next_ctx_s, pid_y, next_ctx, 
                                             current_ctx_, pid_yi, task_y, 
                                             next_thread, current_ctx, pid_ru, 
                                             task_r, next_ctx_, pid_f, task_f, 
                                             pid, current_task, next_task, 
                                             next_thread_, task >>

end_wake(self) == /\ pc[self] = "end_wake"
                  /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = FALSE]
                  /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_task",
                                                              pc        |->  Head(stack[self]).pc,
                                                              task_w    |->  task_w[self] ] >>
                                                          \o Tail(stack[self])]
                     /\ task_w' = [task_w EXCEPT ![self] = task_wa[self]]
                  /\ pc' = [pc EXCEPT ![self] = "start_wake_task"]
                  /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                  lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                  lock_result_context, in_queue, need_sched, 
                                  state, result_next, result_future, 
                                  result_context, result_thread, RUNNING, 
                                  THREADS_pooled, THREADS_running, THREAD_POOL, 
                                  PREEMPTED_TASKS, NEXT_TASK, thread_index, 
                                  thread_is_new, stored_ctx, stored_task, 
                                  thread_to_task, task_to_thread, exec_state, 
                                  preemption_num, wake_other, task_wa, pid_, 
                                  head_, pid_s, head, pid_g, pid_w, task_, 
                                  pid_m, thread, pid_r, pid_t, ctx, pid_se, 
                                  next_ctx_s, pid_y, next_ctx, current_ctx_, 
                                  pid_yi, task_y, next_thread, current_ctx, 
                                  pid_ru, task_r, next_ctx_, pid_f, task_f, 
                                  pid, current_task, next_task, next_thread_, 
                                  task >>

wake(self) == start_wake(self) \/ need_sched_wake(self)
                 \/ wake_but_terminated(self) \/ end_wake(self)

start_preempt_get_next_task(self) == /\ pc[self] = "start_preempt_get_next_task"
                                     /\ ~lock_NEXT_TASK[pid_[self]]
                                     /\ lock_NEXT_TASK' = [lock_NEXT_TASK EXCEPT ![pid_[self]] = TRUE]
                                     /\ pc' = [pc EXCEPT ![self] = "check_preempt_get_next_task"]
                                     /\ UNCHANGED << queue, lock_info, 
                                                     lock_future, 
                                                     lock_scheduler, 
                                                     lock_PREEMPTED_TASKS, 
                                                     lock_result_context, 
                                                     in_queue, need_sched, 
                                                     state, result_next, 
                                                     result_future, 
                                                     result_context, 
                                                     result_thread, RUNNING, 
                                                     THREADS_pooled, 
                                                     THREADS_running, 
                                                     THREAD_POOL, 
                                                     PREEMPTED_TASKS, 
                                                     NEXT_TASK, thread_index, 
                                                     thread_is_new, stored_ctx, 
                                                     stored_task, 
                                                     thread_to_task, 
                                                     task_to_thread, 
                                                     exec_state, 
                                                     preemption_num, 
                                                     wake_other, stack, task_w, 
                                                     task_wa, pid_, head_, 
                                                     pid_s, head, pid_g, pid_w, 
                                                     task_, pid_m, thread, 
                                                     pid_r, pid_t, ctx, pid_se, 
                                                     next_ctx_s, pid_y, 
                                                     next_ctx, current_ctx_, 
                                                     pid_yi, task_y, 
                                                     next_thread, current_ctx, 
                                                     pid_ru, task_r, next_ctx_, 
                                                     pid_f, task_f, pid, 
                                                     current_task, next_task, 
                                                     next_thread_, task >>

check_preempt_get_next_task(self) == /\ pc[self] = "check_preempt_get_next_task"
                                     /\ IF NEXT_TASK[pid_[self]] = <<>>
                                           THEN /\ lock_NEXT_TASK' = [lock_NEXT_TASK EXCEPT ![pid_[self]] = FALSE]
                                                /\ result_next' = [result_next EXCEPT ![pid_[self]] = -1]
                                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                /\ head_' = [head_ EXCEPT ![self] = Head(stack[self]).head_]
                                                /\ pid_' = [pid_ EXCEPT ![self] = Head(stack[self]).pid_]
                                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "pop_preempt_get_next_task"]
                                                /\ UNCHANGED << lock_NEXT_TASK, 
                                                                result_next, 
                                                                stack, pid_, 
                                                                head_ >>
                                     /\ UNCHANGED << queue, lock_info, 
                                                     lock_future, 
                                                     lock_scheduler, 
                                                     lock_PREEMPTED_TASKS, 
                                                     lock_result_context, 
                                                     in_queue, need_sched, 
                                                     state, result_future, 
                                                     result_context, 
                                                     result_thread, RUNNING, 
                                                     THREADS_pooled, 
                                                     THREADS_running, 
                                                     THREAD_POOL, 
                                                     PREEMPTED_TASKS, 
                                                     NEXT_TASK, thread_index, 
                                                     thread_is_new, stored_ctx, 
                                                     stored_task, 
                                                     thread_to_task, 
                                                     task_to_thread, 
                                                     exec_state, 
                                                     preemption_num, 
                                                     wake_other, task_w, 
                                                     task_wa, pid_s, head, 
                                                     pid_g, pid_w, task_, 
                                                     pid_m, thread, pid_r, 
                                                     pid_t, ctx, pid_se, 
                                                     next_ctx_s, pid_y, 
                                                     next_ctx, current_ctx_, 
                                                     pid_yi, task_y, 
                                                     next_thread, current_ctx, 
                                                     pid_ru, task_r, next_ctx_, 
                                                     pid_f, task_f, pid, 
                                                     current_task, next_task, 
                                                     next_thread_, task >>

pop_preempt_get_next_task(self) == /\ pc[self] = "pop_preempt_get_next_task"
                                   /\ head_' = [head_ EXCEPT ![self] = Head(NEXT_TASK[pid_[self]])]
                                   /\ NEXT_TASK' = [NEXT_TASK EXCEPT ![pid_[self]] = Tail(NEXT_TASK[pid_[self]])]
                                   /\ pc' = [pc EXCEPT ![self] = "end_preempt_get_next_task"]
                                   /\ UNCHANGED << queue, lock_info, 
                                                   lock_future, lock_scheduler, 
                                                   lock_PREEMPTED_TASKS, 
                                                   lock_NEXT_TASK, 
                                                   lock_result_context, 
                                                   in_queue, need_sched, state, 
                                                   result_next, result_future, 
                                                   result_context, 
                                                   result_thread, RUNNING, 
                                                   THREADS_pooled, 
                                                   THREADS_running, 
                                                   THREAD_POOL, 
                                                   PREEMPTED_TASKS, 
                                                   thread_index, thread_is_new, 
                                                   stored_ctx, stored_task, 
                                                   thread_to_task, 
                                                   task_to_thread, exec_state, 
                                                   preemption_num, wake_other, 
                                                   stack, task_w, task_wa, 
                                                   pid_, pid_s, head, pid_g, 
                                                   pid_w, task_, pid_m, thread, 
                                                   pid_r, pid_t, ctx, pid_se, 
                                                   next_ctx_s, pid_y, next_ctx, 
                                                   current_ctx_, pid_yi, 
                                                   task_y, next_thread, 
                                                   current_ctx, pid_ru, task_r, 
                                                   next_ctx_, pid_f, task_f, 
                                                   pid, current_task, 
                                                   next_task, next_thread_, 
                                                   task >>

end_preempt_get_next_task(self) == /\ pc[self] = "end_preempt_get_next_task"
                                   /\ lock_NEXT_TASK' = [lock_NEXT_TASK EXCEPT ![pid_[self]] = FALSE]
                                   /\ result_next' = [result_next EXCEPT ![pid_[self]] = head_[self]]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ head_' = [head_ EXCEPT ![self] = Head(stack[self]).head_]
                                   /\ pid_' = [pid_ EXCEPT ![self] = Head(stack[self]).pid_]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   /\ UNCHANGED << queue, lock_info, 
                                                   lock_future, lock_scheduler, 
                                                   lock_PREEMPTED_TASKS, 
                                                   lock_result_context, 
                                                   in_queue, need_sched, state, 
                                                   result_future, 
                                                   result_context, 
                                                   result_thread, RUNNING, 
                                                   THREADS_pooled, 
                                                   THREADS_running, 
                                                   THREAD_POOL, 
                                                   PREEMPTED_TASKS, NEXT_TASK, 
                                                   thread_index, thread_is_new, 
                                                   stored_ctx, stored_task, 
                                                   thread_to_task, 
                                                   task_to_thread, exec_state, 
                                                   preemption_num, wake_other, 
                                                   task_w, task_wa, pid_s, 
                                                   head, pid_g, pid_w, task_, 
                                                   pid_m, thread, pid_r, pid_t, 
                                                   ctx, pid_se, next_ctx_s, 
                                                   pid_y, next_ctx, 
                                                   current_ctx_, pid_yi, 
                                                   task_y, next_thread, 
                                                   current_ctx, pid_ru, task_r, 
                                                   next_ctx_, pid_f, task_f, 
                                                   pid, current_task, 
                                                   next_task, next_thread_, 
                                                   task >>

preempt_get_next_task(self) == start_preempt_get_next_task(self)
                                  \/ check_preempt_get_next_task(self)
                                  \/ pop_preempt_get_next_task(self)
                                  \/ end_preempt_get_next_task(self)

lock_scheduler_get_next(self) == /\ pc[self] = "lock_scheduler_get_next"
                                 /\ ~lock_scheduler
                                 /\ lock_scheduler' = TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "check_scheduler_get_next"]
                                 /\ UNCHANGED << queue, lock_info, lock_future, 
                                                 lock_PREEMPTED_TASKS, 
                                                 lock_NEXT_TASK, 
                                                 lock_result_context, in_queue, 
                                                 need_sched, state, 
                                                 result_next, result_future, 
                                                 result_context, result_thread, 
                                                 RUNNING, THREADS_pooled, 
                                                 THREADS_running, THREAD_POOL, 
                                                 PREEMPTED_TASKS, NEXT_TASK, 
                                                 thread_index, thread_is_new, 
                                                 stored_ctx, stored_task, 
                                                 thread_to_task, 
                                                 task_to_thread, exec_state, 
                                                 preemption_num, wake_other, 
                                                 stack, task_w, task_wa, pid_, 
                                                 head_, pid_s, head, pid_g, 
                                                 pid_w, task_, pid_m, thread, 
                                                 pid_r, pid_t, ctx, pid_se, 
                                                 next_ctx_s, pid_y, next_ctx, 
                                                 current_ctx_, pid_yi, task_y, 
                                                 next_thread, current_ctx, 
                                                 pid_ru, task_r, next_ctx_, 
                                                 pid_f, task_f, pid, 
                                                 current_task, next_task, 
                                                 next_thread_, task >>

check_scheduler_get_next(self) == /\ pc[self] = "check_scheduler_get_next"
                                  /\ IF queue = <<>>
                                        THEN /\ lock_scheduler' = FALSE
                                             /\ result_next' = [result_next EXCEPT ![pid_s[self]] = -1]
                                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                             /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                                             /\ pid_s' = [pid_s EXCEPT ![self] = Head(stack[self]).pid_s]
                                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "pop_scheduler_get_next"]
                                             /\ UNCHANGED << lock_scheduler, 
                                                             result_next, 
                                                             stack, pid_s, 
                                                             head >>
                                  /\ UNCHANGED << queue, lock_info, 
                                                  lock_future, 
                                                  lock_PREEMPTED_TASKS, 
                                                  lock_NEXT_TASK, 
                                                  lock_result_context, 
                                                  in_queue, need_sched, state, 
                                                  result_future, 
                                                  result_context, 
                                                  result_thread, RUNNING, 
                                                  THREADS_pooled, 
                                                  THREADS_running, THREAD_POOL, 
                                                  PREEMPTED_TASKS, NEXT_TASK, 
                                                  thread_index, thread_is_new, 
                                                  stored_ctx, stored_task, 
                                                  thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  preemption_num, wake_other, 
                                                  task_w, task_wa, pid_, head_, 
                                                  pid_g, pid_w, task_, pid_m, 
                                                  thread, pid_r, pid_t, ctx, 
                                                  pid_se, next_ctx_s, pid_y, 
                                                  next_ctx, current_ctx_, 
                                                  pid_yi, task_y, next_thread, 
                                                  current_ctx, pid_ru, task_r, 
                                                  next_ctx_, pid_f, task_f, 
                                                  pid, current_task, next_task, 
                                                  next_thread_, task >>

pop_scheduler_get_next(self) == /\ pc[self] = "pop_scheduler_get_next"
                                /\ head' = [head EXCEPT ![self] = Head(queue)]
                                /\ queue' = Tail(queue)
                                /\ pc' = [pc EXCEPT ![self] = "wait_scheduler_get_next"]
                                /\ UNCHANGED << lock_info, lock_future, 
                                                lock_scheduler, 
                                                lock_PREEMPTED_TASKS, 
                                                lock_NEXT_TASK, 
                                                lock_result_context, in_queue, 
                                                need_sched, state, result_next, 
                                                result_future, result_context, 
                                                result_thread, RUNNING, 
                                                THREADS_pooled, 
                                                THREADS_running, THREAD_POOL, 
                                                PREEMPTED_TASKS, NEXT_TASK, 
                                                thread_index, thread_is_new, 
                                                stored_ctx, stored_task, 
                                                thread_to_task, task_to_thread, 
                                                exec_state, preemption_num, 
                                                wake_other, stack, task_w, 
                                                task_wa, pid_, head_, pid_s, 
                                                pid_g, pid_w, task_, pid_m, 
                                                thread, pid_r, pid_t, ctx, 
                                                pid_se, next_ctx_s, pid_y, 
                                                next_ctx, current_ctx_, pid_yi, 
                                                task_y, next_thread, 
                                                current_ctx, pid_ru, task_r, 
                                                next_ctx_, pid_f, task_f, pid, 
                                                current_task, next_task, 
                                                next_thread_, task >>

wait_scheduler_get_next(self) == /\ pc[self] = "wait_scheduler_get_next"
                                 /\ ~lock_info[head[self]]
                                 /\ lock_info' = [lock_info EXCEPT ![head[self]] = TRUE]
                                 /\ pc' = [pc EXCEPT ![self] = "end_scheduler_get_next"]
                                 /\ UNCHANGED << queue, lock_future, 
                                                 lock_scheduler, 
                                                 lock_PREEMPTED_TASKS, 
                                                 lock_NEXT_TASK, 
                                                 lock_result_context, in_queue, 
                                                 need_sched, state, 
                                                 result_next, result_future, 
                                                 result_context, result_thread, 
                                                 RUNNING, THREADS_pooled, 
                                                 THREADS_running, THREAD_POOL, 
                                                 PREEMPTED_TASKS, NEXT_TASK, 
                                                 thread_index, thread_is_new, 
                                                 stored_ctx, stored_task, 
                                                 thread_to_task, 
                                                 task_to_thread, exec_state, 
                                                 preemption_num, wake_other, 
                                                 stack, task_w, task_wa, pid_, 
                                                 head_, pid_s, head, pid_g, 
                                                 pid_w, task_, pid_m, thread, 
                                                 pid_r, pid_t, ctx, pid_se, 
                                                 next_ctx_s, pid_y, next_ctx, 
                                                 current_ctx_, pid_yi, task_y, 
                                                 next_thread, current_ctx, 
                                                 pid_ru, task_r, next_ctx_, 
                                                 pid_f, task_f, pid, 
                                                 current_task, next_task, 
                                                 next_thread_, task >>

end_scheduler_get_next(self) == /\ pc[self] = "end_scheduler_get_next"
                                /\ in_queue' = [in_queue EXCEPT ![head[self]] = FALSE]
                                /\ state' = [state EXCEPT ![head[self]] = "ReadyToRun"]
                                /\ lock_info' = [lock_info EXCEPT ![head[self]] = FALSE]
                                /\ lock_scheduler' = FALSE
                                /\ result_next' = [result_next EXCEPT ![pid_s[self]] = head[self]]
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ head' = [head EXCEPT ![self] = Head(stack[self]).head]
                                /\ pid_s' = [pid_s EXCEPT ![self] = Head(stack[self]).pid_s]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << queue, lock_future, 
                                                lock_PREEMPTED_TASKS, 
                                                lock_NEXT_TASK, 
                                                lock_result_context, 
                                                need_sched, result_future, 
                                                result_context, result_thread, 
                                                RUNNING, THREADS_pooled, 
                                                THREADS_running, THREAD_POOL, 
                                                PREEMPTED_TASKS, NEXT_TASK, 
                                                thread_index, thread_is_new, 
                                                stored_ctx, stored_task, 
                                                thread_to_task, task_to_thread, 
                                                exec_state, preemption_num, 
                                                wake_other, task_w, task_wa, 
                                                pid_, head_, pid_g, pid_w, 
                                                task_, pid_m, thread, pid_r, 
                                                pid_t, ctx, pid_se, next_ctx_s, 
                                                pid_y, next_ctx, current_ctx_, 
                                                pid_yi, task_y, next_thread, 
                                                current_ctx, pid_ru, task_r, 
                                                next_ctx_, pid_f, task_f, pid, 
                                                current_task, next_task, 
                                                next_thread_, task >>

scheduler_get_next(self) == lock_scheduler_get_next(self)
                               \/ check_scheduler_get_next(self)
                               \/ pop_scheduler_get_next(self)
                               \/ wait_scheduler_get_next(self)
                               \/ end_scheduler_get_next(self)

preempt_get_next_task_(self) == /\ pc[self] = "preempt_get_next_task_"
                                /\ /\ pid_' = [pid_ EXCEPT ![self] = pid_g[self]]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "preempt_get_next_task",
                                                                            pc        |->  "scheduler_get_next_",
                                                                            head_     |->  head_[self],
                                                                            pid_      |->  pid_[self] ] >>
                                                                        \o stack[self]]
                                /\ head_' = [head_ EXCEPT ![self] = defaultInitValue]
                                /\ pc' = [pc EXCEPT ![self] = "start_preempt_get_next_task"]
                                /\ UNCHANGED << queue, lock_info, lock_future, 
                                                lock_scheduler, 
                                                lock_PREEMPTED_TASKS, 
                                                lock_NEXT_TASK, 
                                                lock_result_context, in_queue, 
                                                need_sched, state, result_next, 
                                                result_future, result_context, 
                                                result_thread, RUNNING, 
                                                THREADS_pooled, 
                                                THREADS_running, THREAD_POOL, 
                                                PREEMPTED_TASKS, NEXT_TASK, 
                                                thread_index, thread_is_new, 
                                                stored_ctx, stored_task, 
                                                thread_to_task, task_to_thread, 
                                                exec_state, preemption_num, 
                                                wake_other, task_w, task_wa, 
                                                pid_s, head, pid_g, pid_w, 
                                                task_, pid_m, thread, pid_r, 
                                                pid_t, ctx, pid_se, next_ctx_s, 
                                                pid_y, next_ctx, current_ctx_, 
                                                pid_yi, task_y, next_thread, 
                                                current_ctx, pid_ru, task_r, 
                                                next_ctx_, pid_f, task_f, pid, 
                                                current_task, next_task, 
                                                next_thread_, task >>

scheduler_get_next_(self) == /\ pc[self] = "scheduler_get_next_"
                             /\ IF result_next[pid_g[self]] < 0
                                   THEN /\ /\ pid_s' = [pid_s EXCEPT ![self] = pid_g[self]]
                                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "scheduler_get_next",
                                                                                    pc        |->  "end_get_next_task",
                                                                                    head      |->  head[self],
                                                                                    pid_s     |->  pid_s[self] ] >>
                                                                                \o stack[self]]
                                        /\ head' = [head EXCEPT ![self] = defaultInitValue]
                                        /\ pc' = [pc EXCEPT ![self] = "lock_scheduler_get_next"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "end_get_next_task"]
                                        /\ UNCHANGED << stack, pid_s, head >>
                             /\ UNCHANGED << queue, lock_info, lock_future, 
                                             lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             thread_is_new, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             preemption_num, wake_other, 
                                             task_w, task_wa, pid_, head_, 
                                             pid_g, pid_w, task_, pid_m, 
                                             thread, pid_r, pid_t, ctx, pid_se, 
                                             next_ctx_s, pid_y, next_ctx, 
                                             current_ctx_, pid_yi, task_y, 
                                             next_thread, current_ctx, pid_ru, 
                                             task_r, next_ctx_, pid_f, task_f, 
                                             pid, current_task, next_task, 
                                             next_thread_, task >>

end_get_next_task(self) == /\ pc[self] = "end_get_next_task"
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ pid_g' = [pid_g EXCEPT ![self] = Head(stack[self]).pid_g]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, thread_is_new, 
                                           stored_ctx, stored_task, 
                                           thread_to_task, task_to_thread, 
                                           exec_state, preemption_num, 
                                           wake_other, task_w, task_wa, pid_, 
                                           head_, pid_s, head, pid_w, task_, 
                                           pid_m, thread, pid_r, pid_t, ctx, 
                                           pid_se, next_ctx_s, pid_y, next_ctx, 
                                           current_ctx_, pid_yi, task_y, 
                                           next_thread, current_ctx, pid_ru, 
                                           task_r, next_ctx_, pid_f, task_f, 
                                           pid, current_task, next_task, 
                                           next_thread_, task >>

get_next_task(self) == preempt_get_next_task_(self)
                          \/ scheduler_get_next_(self)
                          \/ end_get_next_task(self)

check_wake_PREEMPTED_TASKS(self) == /\ pc[self] = "check_wake_PREEMPTED_TASKS"
                                    /\ IF PREEMPTED_TASKS[pid_w[self]] = <<>>
                                          THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                               /\ task_' = [task_ EXCEPT ![self] = Head(stack[self]).task_]
                                               /\ pid_w' = [pid_w EXCEPT ![self] = Head(stack[self]).pid_w]
                                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "pop_wake_PREEMPTED_TASKS"]
                                               /\ UNCHANGED << stack, pid_w, 
                                                               task_ >>
                                    /\ UNCHANGED << queue, lock_info, 
                                                    lock_future, 
                                                    lock_scheduler, 
                                                    lock_PREEMPTED_TASKS, 
                                                    lock_NEXT_TASK, 
                                                    lock_result_context, 
                                                    in_queue, need_sched, 
                                                    state, result_next, 
                                                    result_future, 
                                                    result_context, 
                                                    result_thread, RUNNING, 
                                                    THREADS_pooled, 
                                                    THREADS_running, 
                                                    THREAD_POOL, 
                                                    PREEMPTED_TASKS, NEXT_TASK, 
                                                    thread_index, 
                                                    thread_is_new, stored_ctx, 
                                                    stored_task, 
                                                    thread_to_task, 
                                                    task_to_thread, exec_state, 
                                                    preemption_num, wake_other, 
                                                    task_w, task_wa, pid_, 
                                                    head_, pid_s, head, pid_g, 
                                                    pid_m, thread, pid_r, 
                                                    pid_t, ctx, pid_se, 
                                                    next_ctx_s, pid_y, 
                                                    next_ctx, current_ctx_, 
                                                    pid_yi, task_y, 
                                                    next_thread, current_ctx, 
                                                    pid_ru, task_r, next_ctx_, 
                                                    pid_f, task_f, pid, 
                                                    current_task, next_task, 
                                                    next_thread_, task >>

pop_wake_PREEMPTED_TASKS(self) == /\ pc[self] = "pop_wake_PREEMPTED_TASKS"
                                  /\ task_' = [task_ EXCEPT ![self] = Head(PREEMPTED_TASKS[pid_w[self]])]
                                  /\ PREEMPTED_TASKS' = [PREEMPTED_TASKS EXCEPT ![pid_w[self]] = Tail(PREEMPTED_TASKS[pid_w[self]])]
                                  /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_task",
                                                                              pc        |->  "end_wake_PREEMPTED_TASKS",
                                                                              task_w    |->  task_w[self] ] >>
                                                                          \o stack[self]]
                                     /\ task_w' = [task_w EXCEPT ![self] = task_'[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "start_wake_task"]
                                  /\ UNCHANGED << queue, lock_info, 
                                                  lock_future, lock_scheduler, 
                                                  lock_PREEMPTED_TASKS, 
                                                  lock_NEXT_TASK, 
                                                  lock_result_context, 
                                                  in_queue, need_sched, state, 
                                                  result_next, result_future, 
                                                  result_context, 
                                                  result_thread, RUNNING, 
                                                  THREADS_pooled, 
                                                  THREADS_running, THREAD_POOL, 
                                                  NEXT_TASK, thread_index, 
                                                  thread_is_new, stored_ctx, 
                                                  stored_task, thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  preemption_num, wake_other, 
                                                  task_wa, pid_, head_, pid_s, 
                                                  head, pid_g, pid_w, pid_m, 
                                                  thread, pid_r, pid_t, ctx, 
                                                  pid_se, next_ctx_s, pid_y, 
                                                  next_ctx, current_ctx_, 
                                                  pid_yi, task_y, next_thread, 
                                                  current_ctx, pid_ru, task_r, 
                                                  next_ctx_, pid_f, task_f, 
                                                  pid, current_task, next_task, 
                                                  next_thread_, task >>

end_wake_PREEMPTED_TASKS(self) == /\ pc[self] = "end_wake_PREEMPTED_TASKS"
                                  /\ pid_w' = [pid_w EXCEPT ![self] = pid_w[self]]
                                  /\ task_' = [task_ EXCEPT ![self] = defaultInitValue]
                                  /\ pc' = [pc EXCEPT ![self] = "check_wake_PREEMPTED_TASKS"]
                                  /\ UNCHANGED << queue, lock_info, 
                                                  lock_future, lock_scheduler, 
                                                  lock_PREEMPTED_TASKS, 
                                                  lock_NEXT_TASK, 
                                                  lock_result_context, 
                                                  in_queue, need_sched, state, 
                                                  result_next, result_future, 
                                                  result_context, 
                                                  result_thread, RUNNING, 
                                                  THREADS_pooled, 
                                                  THREADS_running, THREAD_POOL, 
                                                  PREEMPTED_TASKS, NEXT_TASK, 
                                                  thread_index, thread_is_new, 
                                                  stored_ctx, stored_task, 
                                                  thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  preemption_num, wake_other, 
                                                  stack, task_w, task_wa, pid_, 
                                                  head_, pid_s, head, pid_g, 
                                                  pid_m, thread, pid_r, pid_t, 
                                                  ctx, pid_se, next_ctx_s, 
                                                  pid_y, next_ctx, 
                                                  current_ctx_, pid_yi, task_y, 
                                                  next_thread, current_ctx, 
                                                  pid_ru, task_r, next_ctx_, 
                                                  pid_f, task_f, pid, 
                                                  current_task, next_task, 
                                                  next_thread_, task >>

wake_PREEMPTED_TASKS(self) == check_wake_PREEMPTED_TASKS(self)
                                 \/ pop_wake_PREEMPTED_TASKS(self)
                                 \/ end_wake_PREEMPTED_TASKS(self)

check_make_all_threads_pooled(self) == /\ pc[self] = "check_make_all_threads_pooled"
                                       /\ IF THREAD_POOL[pid_m[self]] = <<>>
                                             THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                  /\ thread' = [thread EXCEPT ![self] = Head(stack[self]).thread]
                                                  /\ pid_m' = [pid_m EXCEPT ![self] = Head(stack[self]).pid_m]
                                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "pop_make_all_threads_pooled"]
                                                  /\ UNCHANGED << stack, pid_m, 
                                                                  thread >>
                                       /\ UNCHANGED << queue, lock_info, 
                                                       lock_future, 
                                                       lock_scheduler, 
                                                       lock_PREEMPTED_TASKS, 
                                                       lock_NEXT_TASK, 
                                                       lock_result_context, 
                                                       in_queue, need_sched, 
                                                       state, result_next, 
                                                       result_future, 
                                                       result_context, 
                                                       result_thread, RUNNING, 
                                                       THREADS_pooled, 
                                                       THREADS_running, 
                                                       THREAD_POOL, 
                                                       PREEMPTED_TASKS, 
                                                       NEXT_TASK, thread_index, 
                                                       thread_is_new, 
                                                       stored_ctx, stored_task, 
                                                       thread_to_task, 
                                                       task_to_thread, 
                                                       exec_state, 
                                                       preemption_num, 
                                                       wake_other, task_w, 
                                                       task_wa, pid_, head_, 
                                                       pid_s, head, pid_g, 
                                                       pid_w, task_, pid_r, 
                                                       pid_t, ctx, pid_se, 
                                                       next_ctx_s, pid_y, 
                                                       next_ctx, current_ctx_, 
                                                       pid_yi, task_y, 
                                                       next_thread, 
                                                       current_ctx, pid_ru, 
                                                       task_r, next_ctx_, 
                                                       pid_f, task_f, pid, 
                                                       current_task, next_task, 
                                                       next_thread_, task >>

pop_make_all_threads_pooled(self) == /\ pc[self] = "pop_make_all_threads_pooled"
                                     /\ thread' = [thread EXCEPT ![self] = Head(THREAD_POOL[pid_m[self]])]
                                     /\ THREAD_POOL' = [THREAD_POOL EXCEPT ![pid_m[self]] = Tail(THREAD_POOL[pid_m[self]])]
                                     /\ THREADS_pooled' = Append(THREADS_pooled, thread'[self])
                                     /\ pc' = [pc EXCEPT ![self] = "end_make_all_threads_pooled"]
                                     /\ UNCHANGED << queue, lock_info, 
                                                     lock_future, 
                                                     lock_scheduler, 
                                                     lock_PREEMPTED_TASKS, 
                                                     lock_NEXT_TASK, 
                                                     lock_result_context, 
                                                     in_queue, need_sched, 
                                                     state, result_next, 
                                                     result_future, 
                                                     result_context, 
                                                     result_thread, RUNNING, 
                                                     THREADS_running, 
                                                     PREEMPTED_TASKS, 
                                                     NEXT_TASK, thread_index, 
                                                     thread_is_new, stored_ctx, 
                                                     stored_task, 
                                                     thread_to_task, 
                                                     task_to_thread, 
                                                     exec_state, 
                                                     preemption_num, 
                                                     wake_other, stack, task_w, 
                                                     task_wa, pid_, head_, 
                                                     pid_s, head, pid_g, pid_w, 
                                                     task_, pid_m, pid_r, 
                                                     pid_t, ctx, pid_se, 
                                                     next_ctx_s, pid_y, 
                                                     next_ctx, current_ctx_, 
                                                     pid_yi, task_y, 
                                                     next_thread, current_ctx, 
                                                     pid_ru, task_r, next_ctx_, 
                                                     pid_f, task_f, pid, 
                                                     current_task, next_task, 
                                                     next_thread_, task >>

end_make_all_threads_pooled(self) == /\ pc[self] = "end_make_all_threads_pooled"
                                     /\ pid_m' = [pid_m EXCEPT ![self] = pid_m[self]]
                                     /\ thread' = [thread EXCEPT ![self] = defaultInitValue]
                                     /\ pc' = [pc EXCEPT ![self] = "check_make_all_threads_pooled"]
                                     /\ UNCHANGED << queue, lock_info, 
                                                     lock_future, 
                                                     lock_scheduler, 
                                                     lock_PREEMPTED_TASKS, 
                                                     lock_NEXT_TASK, 
                                                     lock_result_context, 
                                                     in_queue, need_sched, 
                                                     state, result_next, 
                                                     result_future, 
                                                     result_context, 
                                                     result_thread, RUNNING, 
                                                     THREADS_pooled, 
                                                     THREADS_running, 
                                                     THREAD_POOL, 
                                                     PREEMPTED_TASKS, 
                                                     NEXT_TASK, thread_index, 
                                                     thread_is_new, stored_ctx, 
                                                     stored_task, 
                                                     thread_to_task, 
                                                     task_to_thread, 
                                                     exec_state, 
                                                     preemption_num, 
                                                     wake_other, stack, task_w, 
                                                     task_wa, pid_, head_, 
                                                     pid_s, head, pid_g, pid_w, 
                                                     task_, pid_r, pid_t, ctx, 
                                                     pid_se, next_ctx_s, pid_y, 
                                                     next_ctx, current_ctx_, 
                                                     pid_yi, task_y, 
                                                     next_thread, current_ctx, 
                                                     pid_ru, task_r, next_ctx_, 
                                                     pid_f, task_f, pid, 
                                                     current_task, next_task, 
                                                     next_thread_, task >>

make_all_threads_pooled(self) == check_make_all_threads_pooled(self)
                                    \/ pop_make_all_threads_pooled(self)
                                    \/ end_make_all_threads_pooled(self)

lock_preempted_re_schedule(self) == /\ pc[self] = "lock_preempted_re_schedule"
                                    /\ ~lock_PREEMPTED_TASKS[pid_r[self]]
                                    /\ lock_PREEMPTED_TASKS' = [lock_PREEMPTED_TASKS EXCEPT ![pid_r[self]] = TRUE]
                                    /\ pc' = [pc EXCEPT ![self] = "wake_re_schedule"]
                                    /\ UNCHANGED << queue, lock_info, 
                                                    lock_future, 
                                                    lock_scheduler, 
                                                    lock_NEXT_TASK, 
                                                    lock_result_context, 
                                                    in_queue, need_sched, 
                                                    state, result_next, 
                                                    result_future, 
                                                    result_context, 
                                                    result_thread, RUNNING, 
                                                    THREADS_pooled, 
                                                    THREADS_running, 
                                                    THREAD_POOL, 
                                                    PREEMPTED_TASKS, NEXT_TASK, 
                                                    thread_index, 
                                                    thread_is_new, stored_ctx, 
                                                    stored_task, 
                                                    thread_to_task, 
                                                    task_to_thread, exec_state, 
                                                    preemption_num, wake_other, 
                                                    stack, task_w, task_wa, 
                                                    pid_, head_, pid_s, head, 
                                                    pid_g, pid_w, task_, pid_m, 
                                                    thread, pid_r, pid_t, ctx, 
                                                    pid_se, next_ctx_s, pid_y, 
                                                    next_ctx, current_ctx_, 
                                                    pid_yi, task_y, 
                                                    next_thread, current_ctx, 
                                                    pid_ru, task_r, next_ctx_, 
                                                    pid_f, task_f, pid, 
                                                    current_task, next_task, 
                                                    next_thread_, task >>

wake_re_schedule(self) == /\ pc[self] = "wake_re_schedule"
                          /\ /\ pid_w' = [pid_w EXCEPT ![self] = pid_r[self]]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_PREEMPTED_TASKS",
                                                                      pc        |->  "unlock_preempted_re_schedule",
                                                                      task_     |->  task_[self],
                                                                      pid_w     |->  pid_w[self] ] >>
                                                                  \o stack[self]]
                          /\ task_' = [task_ EXCEPT ![self] = defaultInitValue]
                          /\ pc' = [pc EXCEPT ![self] = "check_wake_PREEMPTED_TASKS"]
                          /\ UNCHANGED << queue, lock_info, lock_future, 
                                          lock_scheduler, lock_PREEMPTED_TASKS, 
                                          lock_NEXT_TASK, lock_result_context, 
                                          in_queue, need_sched, state, 
                                          result_next, result_future, 
                                          result_context, result_thread, 
                                          RUNNING, THREADS_pooled, 
                                          THREADS_running, THREAD_POOL, 
                                          PREEMPTED_TASKS, NEXT_TASK, 
                                          thread_index, thread_is_new, 
                                          stored_ctx, stored_task, 
                                          thread_to_task, task_to_thread, 
                                          exec_state, preemption_num, 
                                          wake_other, task_w, task_wa, pid_, 
                                          head_, pid_s, head, pid_g, pid_m, 
                                          thread, pid_r, pid_t, ctx, pid_se, 
                                          next_ctx_s, pid_y, next_ctx, 
                                          current_ctx_, pid_yi, task_y, 
                                          next_thread, current_ctx, pid_ru, 
                                          task_r, next_ctx_, pid_f, task_f, 
                                          pid, current_task, next_task, 
                                          next_thread_, task >>

unlock_preempted_re_schedule(self) == /\ pc[self] = "unlock_preempted_re_schedule"
                                      /\ lock_PREEMPTED_TASKS' = [lock_PREEMPTED_TASKS EXCEPT ![pid_r[self]] = FALSE]
                                      /\ pc' = [pc EXCEPT ![self] = "pool_re_schedule"]
                                      /\ UNCHANGED << queue, lock_info, 
                                                      lock_future, 
                                                      lock_scheduler, 
                                                      lock_NEXT_TASK, 
                                                      lock_result_context, 
                                                      in_queue, need_sched, 
                                                      state, result_next, 
                                                      result_future, 
                                                      result_context, 
                                                      result_thread, RUNNING, 
                                                      THREADS_pooled, 
                                                      THREADS_running, 
                                                      THREAD_POOL, 
                                                      PREEMPTED_TASKS, 
                                                      NEXT_TASK, thread_index, 
                                                      thread_is_new, 
                                                      stored_ctx, stored_task, 
                                                      thread_to_task, 
                                                      task_to_thread, 
                                                      exec_state, 
                                                      preemption_num, 
                                                      wake_other, stack, 
                                                      task_w, task_wa, pid_, 
                                                      head_, pid_s, head, 
                                                      pid_g, pid_w, task_, 
                                                      pid_m, thread, pid_r, 
                                                      pid_t, ctx, pid_se, 
                                                      next_ctx_s, pid_y, 
                                                      next_ctx, current_ctx_, 
                                                      pid_yi, task_y, 
                                                      next_thread, current_ctx, 
                                                      pid_ru, task_r, 
                                                      next_ctx_, pid_f, task_f, 
                                                      pid, current_task, 
                                                      next_task, next_thread_, 
                                                      task >>

pool_re_schedule(self) == /\ pc[self] = "pool_re_schedule"
                          /\ /\ pid_m' = [pid_m EXCEPT ![self] = pid_r[self]]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "make_all_threads_pooled",
                                                                      pc        |->  "end_re_schedule",
                                                                      thread    |->  thread[self],
                                                                      pid_m     |->  pid_m[self] ] >>
                                                                  \o stack[self]]
                          /\ thread' = [thread EXCEPT ![self] = defaultInitValue]
                          /\ pc' = [pc EXCEPT ![self] = "check_make_all_threads_pooled"]
                          /\ UNCHANGED << queue, lock_info, lock_future, 
                                          lock_scheduler, lock_PREEMPTED_TASKS, 
                                          lock_NEXT_TASK, lock_result_context, 
                                          in_queue, need_sched, state, 
                                          result_next, result_future, 
                                          result_context, result_thread, 
                                          RUNNING, THREADS_pooled, 
                                          THREADS_running, THREAD_POOL, 
                                          PREEMPTED_TASKS, NEXT_TASK, 
                                          thread_index, thread_is_new, 
                                          stored_ctx, stored_task, 
                                          thread_to_task, task_to_thread, 
                                          exec_state, preemption_num, 
                                          wake_other, task_w, task_wa, pid_, 
                                          head_, pid_s, head, pid_g, pid_w, 
                                          task_, pid_r, pid_t, ctx, pid_se, 
                                          next_ctx_s, pid_y, next_ctx, 
                                          current_ctx_, pid_yi, task_y, 
                                          next_thread, current_ctx, pid_ru, 
                                          task_r, next_ctx_, pid_f, task_f, 
                                          pid, current_task, next_task, 
                                          next_thread_, task >>

end_re_schedule(self) == /\ pc[self] = "end_re_schedule"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ pid_r' = [pid_r EXCEPT ![self] = Head(stack[self]).pid_r]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << queue, lock_info, lock_future, 
                                         lock_scheduler, lock_PREEMPTED_TASKS, 
                                         lock_NEXT_TASK, lock_result_context, 
                                         in_queue, need_sched, state, 
                                         result_next, result_future, 
                                         result_context, result_thread, 
                                         RUNNING, THREADS_pooled, 
                                         THREADS_running, THREAD_POOL, 
                                         PREEMPTED_TASKS, NEXT_TASK, 
                                         thread_index, thread_is_new, 
                                         stored_ctx, stored_task, 
                                         thread_to_task, task_to_thread, 
                                         exec_state, preemption_num, 
                                         wake_other, task_w, task_wa, pid_, 
                                         head_, pid_s, head, pid_g, pid_w, 
                                         task_, pid_m, thread, pid_t, ctx, 
                                         pid_se, next_ctx_s, pid_y, next_ctx, 
                                         current_ctx_, pid_yi, task_y, 
                                         next_thread, current_ctx, pid_ru, 
                                         task_r, next_ctx_, pid_f, task_f, pid, 
                                         current_task, next_task, next_thread_, 
                                         task >>

re_schedule(self) == lock_preempted_re_schedule(self)
                        \/ wake_re_schedule(self)
                        \/ unlock_preempted_re_schedule(self)
                        \/ pool_re_schedule(self) \/ end_re_schedule(self)

start_thread_entry(self) == /\ pc[self] = "start_thread_entry"
                            /\ THREADS_running' = [THREADS_running EXCEPT ![pid_t[self]] = ctx[self]]
                            /\ /\ pid_r' = [pid_r EXCEPT ![self] = pid_t[self]]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "re_schedule",
                                                                        pc        |->  "run_main_thread_entry",
                                                                        pid_r     |->  pid_r[self] ] >>
                                                                    \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "lock_preempted_re_schedule"]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, state, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREAD_POOL, 
                                            PREEMPTED_TASKS, NEXT_TASK, 
                                            thread_index, thread_is_new, 
                                            stored_ctx, stored_task, 
                                            thread_to_task, task_to_thread, 
                                            exec_state, preemption_num, 
                                            wake_other, task_w, task_wa, pid_, 
                                            head_, pid_s, head, pid_g, pid_w, 
                                            task_, pid_m, thread, pid_t, ctx, 
                                            pid_se, next_ctx_s, pid_y, 
                                            next_ctx, current_ctx_, pid_yi, 
                                            task_y, next_thread, current_ctx, 
                                            pid_ru, task_r, next_ctx_, pid_f, 
                                            task_f, pid, current_task, 
                                            next_task, next_thread_, task >>

run_main_thread_entry(self) == /\ pc[self] = "run_main_thread_entry"
                               /\ /\ pid_ru' = [pid_ru EXCEPT ![self] = pid_t[self]]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "run_main",
                                                                           pc        |->  "end_thread_entry",
                                                                           task_r    |->  task_r[self],
                                                                           next_ctx_ |->  next_ctx_[self],
                                                                           pid_ru    |->  pid_ru[self] ] >>
                                                                       \o stack[self]]
                               /\ task_r' = [task_r EXCEPT ![self] = defaultInitValue]
                               /\ next_ctx_' = [next_ctx_ EXCEPT ![self] = defaultInitValue]
                               /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                               /\ UNCHANGED << queue, lock_info, lock_future, 
                                               lock_scheduler, 
                                               lock_PREEMPTED_TASKS, 
                                               lock_NEXT_TASK, 
                                               lock_result_context, in_queue, 
                                               need_sched, state, result_next, 
                                               result_future, result_context, 
                                               result_thread, RUNNING, 
                                               THREADS_pooled, THREADS_running, 
                                               THREAD_POOL, PREEMPTED_TASKS, 
                                               NEXT_TASK, thread_index, 
                                               thread_is_new, stored_ctx, 
                                               stored_task, thread_to_task, 
                                               task_to_thread, exec_state, 
                                               preemption_num, wake_other, 
                                               task_w, task_wa, pid_, head_, 
                                               pid_s, head, pid_g, pid_w, 
                                               task_, pid_m, thread, pid_r, 
                                               pid_t, ctx, pid_se, next_ctx_s, 
                                               pid_y, next_ctx, current_ctx_, 
                                               pid_yi, task_y, next_thread, 
                                               current_ctx, pid_f, task_f, pid, 
                                               current_task, next_task, 
                                               next_thread_, task >>

end_thread_entry(self) == /\ pc[self] = "end_thread_entry"
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ pid_t' = [pid_t EXCEPT ![self] = Head(stack[self]).pid_t]
                          /\ ctx' = [ctx EXCEPT ![self] = Head(stack[self]).ctx]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << queue, lock_info, lock_future, 
                                          lock_scheduler, lock_PREEMPTED_TASKS, 
                                          lock_NEXT_TASK, lock_result_context, 
                                          in_queue, need_sched, state, 
                                          result_next, result_future, 
                                          result_context, result_thread, 
                                          RUNNING, THREADS_pooled, 
                                          THREADS_running, THREAD_POOL, 
                                          PREEMPTED_TASKS, NEXT_TASK, 
                                          thread_index, thread_is_new, 
                                          stored_ctx, stored_task, 
                                          thread_to_task, task_to_thread, 
                                          exec_state, preemption_num, 
                                          wake_other, task_w, task_wa, pid_, 
                                          head_, pid_s, head, pid_g, pid_w, 
                                          task_, pid_m, thread, pid_r, pid_se, 
                                          next_ctx_s, pid_y, next_ctx, 
                                          current_ctx_, pid_yi, task_y, 
                                          next_thread, current_ctx, pid_ru, 
                                          task_r, next_ctx_, pid_f, task_f, 
                                          pid, current_task, next_task, 
                                          next_thread_, task >>

thread_entry(self) == start_thread_entry(self)
                         \/ run_main_thread_entry(self)
                         \/ end_thread_entry(self)

start_set_exec_state(self) == /\ pc[self] = "start_set_exec_state"
                              /\ THREADS_running' = [THREADS_running EXCEPT ![pid_se[self]] = next_ctx_s[self]]
                              /\ next_task' = [next_task EXCEPT ![self] = thread_to_task[next_ctx_s[self]]]
                              /\ IF next_task'[self] > 0
                                    THEN /\ RUNNING' = [RUNNING EXCEPT ![pid_se[self]] = next_task'[self]]
                                         /\ exec_state' = [exec_state EXCEPT ![pid_se[self]] = "Preempted"]
                                         /\ pc' = [pc EXCEPT ![self] = "end_set_exec_state"]
                                         /\ UNCHANGED << thread_is_new, stack, 
                                                         pid_t, ctx >>
                                    ELSE /\ IF thread_is_new[next_ctx_s[self]] = TRUE
                                               THEN /\ thread_is_new' = [thread_is_new EXCEPT ![next_ctx_s[self]] = FALSE]
                                                    /\ /\ ctx' = [ctx EXCEPT ![self] = next_ctx_s[self]]
                                                       /\ pid_t' = [pid_t EXCEPT ![self] = pid_se[self]]
                                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "thread_entry",
                                                                                                pc        |->  "end_set_exec_state",
                                                                                                pid_t     |->  pid_t[self],
                                                                                                ctx       |->  ctx[self] ] >>
                                                                                            \o stack[self]]
                                                    /\ pc' = [pc EXCEPT ![self] = "start_thread_entry"]
                                                    /\ UNCHANGED exec_state
                                               ELSE /\ exec_state' = [exec_state EXCEPT ![pid_se[self]] = "Yielded"]
                                                    /\ pc' = [pc EXCEPT ![self] = "end_set_exec_state"]
                                                    /\ UNCHANGED << thread_is_new, 
                                                                    stack, 
                                                                    pid_t, ctx >>
                                         /\ UNCHANGED RUNNING
                              /\ UNCHANGED << queue, lock_info, lock_future, 
                                              lock_scheduler, 
                                              lock_PREEMPTED_TASKS, 
                                              lock_NEXT_TASK, 
                                              lock_result_context, in_queue, 
                                              need_sched, state, result_next, 
                                              result_future, result_context, 
                                              result_thread, THREADS_pooled, 
                                              THREAD_POOL, PREEMPTED_TASKS, 
                                              NEXT_TASK, thread_index, 
                                              stored_ctx, stored_task, 
                                              thread_to_task, task_to_thread, 
                                              preemption_num, wake_other, 
                                              task_w, task_wa, pid_, head_, 
                                              pid_s, head, pid_g, pid_w, task_, 
                                              pid_m, thread, pid_r, pid_se, 
                                              next_ctx_s, pid_y, next_ctx, 
                                              current_ctx_, pid_yi, task_y, 
                                              next_thread, current_ctx, pid_ru, 
                                              task_r, next_ctx_, pid_f, task_f, 
                                              pid, current_task, next_thread_, 
                                              task >>

end_set_exec_state(self) == /\ pc[self] = "end_set_exec_state"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ pid_se' = [pid_se EXCEPT ![self] = Head(stack[self]).pid_se]
                            /\ next_ctx_s' = [next_ctx_s EXCEPT ![self] = Head(stack[self]).next_ctx_s]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, state, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREADS_running, 
                                            THREAD_POOL, PREEMPTED_TASKS, 
                                            NEXT_TASK, thread_index, 
                                            thread_is_new, stored_ctx, 
                                            stored_task, thread_to_task, 
                                            task_to_thread, exec_state, 
                                            preemption_num, wake_other, task_w, 
                                            task_wa, pid_, head_, pid_s, head, 
                                            pid_g, pid_w, task_, pid_m, thread, 
                                            pid_r, pid_t, ctx, pid_y, next_ctx, 
                                            current_ctx_, pid_yi, task_y, 
                                            next_thread, current_ctx, pid_ru, 
                                            task_r, next_ctx_, pid_f, task_f, 
                                            pid, current_task, next_task, 
                                            next_thread_, task >>

set_exec_state(self) == start_set_exec_state(self)
                           \/ end_set_exec_state(self)

start_yield_and_pool(self) == /\ pc[self] = "start_yield_and_pool"
                              /\ IF exec_state[pid_y[self]] = "Init"
                                    THEN /\ pc' = [pc EXCEPT ![self] = "lock_result_yield_and_pool"]
                                         /\ UNCHANGED << exec_state, 
                                                         current_ctx_ >>
                                    ELSE /\ IF exec_state[pid_y[self]] = "Yielded"
                                               THEN /\ exec_state' = [exec_state EXCEPT ![pid_y[self]] = "Init"]
                                                    /\ current_ctx_' = [current_ctx_ EXCEPT ![self] = stored_ctx[pid_y[self]]]
                                                    /\ pc' = [pc EXCEPT ![self] = "re_schedule_yield_and_pool"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "lock_result_yield_and_pool"]
                                                    /\ UNCHANGED << exec_state, 
                                                                    current_ctx_ >>
                              /\ UNCHANGED << queue, lock_info, lock_future, 
                                              lock_scheduler, 
                                              lock_PREEMPTED_TASKS, 
                                              lock_NEXT_TASK, 
                                              lock_result_context, in_queue, 
                                              need_sched, state, result_next, 
                                              result_future, result_context, 
                                              result_thread, RUNNING, 
                                              THREADS_pooled, THREADS_running, 
                                              THREAD_POOL, PREEMPTED_TASKS, 
                                              NEXT_TASK, thread_index, 
                                              thread_is_new, stored_ctx, 
                                              stored_task, thread_to_task, 
                                              task_to_thread, preemption_num, 
                                              wake_other, stack, task_w, 
                                              task_wa, pid_, head_, pid_s, 
                                              head, pid_g, pid_w, task_, pid_m, 
                                              thread, pid_r, pid_t, ctx, 
                                              pid_se, next_ctx_s, pid_y, 
                                              next_ctx, pid_yi, task_y, 
                                              next_thread, current_ctx, pid_ru, 
                                              task_r, next_ctx_, pid_f, task_f, 
                                              pid, current_task, next_task, 
                                              next_thread_, task >>

lock_result_yield_and_pool(self) == /\ pc[self] = "lock_result_yield_and_pool"
                                    /\ ~lock_result_context
                                    /\ lock_result_context' = TRUE
                                    /\ result_context' = THREADS_running[pid_y[self]]
                                    /\ THREADS_running' = [THREADS_running EXCEPT ![pid_y[self]] = -1]
                                    /\ pc' = [pc EXCEPT ![self] = "unlock_result_yield_and_pool"]
                                    /\ UNCHANGED << queue, lock_info, 
                                                    lock_future, 
                                                    lock_scheduler, 
                                                    lock_PREEMPTED_TASKS, 
                                                    lock_NEXT_TASK, in_queue, 
                                                    need_sched, state, 
                                                    result_next, result_future, 
                                                    result_thread, RUNNING, 
                                                    THREADS_pooled, 
                                                    THREAD_POOL, 
                                                    PREEMPTED_TASKS, NEXT_TASK, 
                                                    thread_index, 
                                                    thread_is_new, stored_ctx, 
                                                    stored_task, 
                                                    thread_to_task, 
                                                    task_to_thread, exec_state, 
                                                    preemption_num, wake_other, 
                                                    stack, task_w, task_wa, 
                                                    pid_, head_, pid_s, head, 
                                                    pid_g, pid_w, task_, pid_m, 
                                                    thread, pid_r, pid_t, ctx, 
                                                    pid_se, next_ctx_s, pid_y, 
                                                    next_ctx, current_ctx_, 
                                                    pid_yi, task_y, 
                                                    next_thread, current_ctx, 
                                                    pid_ru, task_r, next_ctx_, 
                                                    pid_f, task_f, pid, 
                                                    current_task, next_task, 
                                                    next_thread_, task >>

unlock_result_yield_and_pool(self) == /\ pc[self] = "unlock_result_yield_and_pool"
                                      /\ current_ctx_' = [current_ctx_ EXCEPT ![self] = result_context]
                                      /\ lock_result_context' = FALSE
                                      /\ THREAD_POOL' = [THREAD_POOL EXCEPT ![pid_y[self]] = Append(THREAD_POOL[pid_y[self]], current_ctx_'[self])]
                                      /\ pc' = [pc EXCEPT ![self] = "context_switch_yield_and_pool"]
                                      /\ UNCHANGED << queue, lock_info, 
                                                      lock_future, 
                                                      lock_scheduler, 
                                                      lock_PREEMPTED_TASKS, 
                                                      lock_NEXT_TASK, in_queue, 
                                                      need_sched, state, 
                                                      result_next, 
                                                      result_future, 
                                                      result_context, 
                                                      result_thread, RUNNING, 
                                                      THREADS_pooled, 
                                                      THREADS_running, 
                                                      PREEMPTED_TASKS, 
                                                      NEXT_TASK, thread_index, 
                                                      thread_is_new, 
                                                      stored_ctx, stored_task, 
                                                      thread_to_task, 
                                                      task_to_thread, 
                                                      exec_state, 
                                                      preemption_num, 
                                                      wake_other, stack, 
                                                      task_w, task_wa, pid_, 
                                                      head_, pid_s, head, 
                                                      pid_g, pid_w, task_, 
                                                      pid_m, thread, pid_r, 
                                                      pid_t, ctx, pid_se, 
                                                      next_ctx_s, pid_y, 
                                                      next_ctx, pid_yi, task_y, 
                                                      next_thread, current_ctx, 
                                                      pid_ru, task_r, 
                                                      next_ctx_, pid_f, task_f, 
                                                      pid, current_task, 
                                                      next_task, next_thread_, 
                                                      task >>

context_switch_yield_and_pool(self) == /\ pc[self] = "context_switch_yield_and_pool"
                                       /\ stored_task' = [stored_task EXCEPT ![pid_y[self]] = thread_to_task[next_ctx[self]]]
                                       /\ stored_ctx' = [stored_ctx EXCEPT ![pid_y[self]] = next_ctx[self]]
                                       /\ /\ current_ctx_' = [current_ctx_ EXCEPT ![self] = Head(stack[self]).current_ctx_]
                                          /\ next_ctx_s' = [next_ctx_s EXCEPT ![self] = next_ctx[self]]
                                          /\ pid_se' = [pid_se EXCEPT ![self] = pid_y[self]]
                                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_exec_state",
                                                                                   pc        |->  Head(stack[self]).pc,
                                                                                   pid_se    |->  pid_se[self],
                                                                                   next_ctx_s |->  next_ctx_s[self] ] >>
                                                                               \o Tail(stack[self])]
                                       /\ pc' = [pc EXCEPT ![self] = "start_set_exec_state"]
                                       /\ UNCHANGED << queue, lock_info, 
                                                       lock_future, 
                                                       lock_scheduler, 
                                                       lock_PREEMPTED_TASKS, 
                                                       lock_NEXT_TASK, 
                                                       lock_result_context, 
                                                       in_queue, need_sched, 
                                                       state, result_next, 
                                                       result_future, 
                                                       result_context, 
                                                       result_thread, RUNNING, 
                                                       THREADS_pooled, 
                                                       THREADS_running, 
                                                       THREAD_POOL, 
                                                       PREEMPTED_TASKS, 
                                                       NEXT_TASK, thread_index, 
                                                       thread_is_new, 
                                                       thread_to_task, 
                                                       task_to_thread, 
                                                       exec_state, 
                                                       preemption_num, 
                                                       wake_other, task_w, 
                                                       task_wa, pid_, head_, 
                                                       pid_s, head, pid_g, 
                                                       pid_w, task_, pid_m, 
                                                       thread, pid_r, pid_t, 
                                                       ctx, pid_y, next_ctx, 
                                                       pid_yi, task_y, 
                                                       next_thread, 
                                                       current_ctx, pid_ru, 
                                                       task_r, next_ctx_, 
                                                       pid_f, task_f, pid, 
                                                       current_task, next_task, 
                                                       next_thread_, task >>

re_schedule_yield_and_pool(self) == /\ pc[self] = "re_schedule_yield_and_pool"
                                    /\ THREADS_running' = [THREADS_running EXCEPT ![pid_y[self]] = current_ctx_[self]]
                                    /\ /\ pid_r' = [pid_r EXCEPT ![self] = pid_y[self]]
                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "re_schedule",
                                                                                pc        |->  "end_yield_and_pool",
                                                                                pid_r     |->  pid_r[self] ] >>
                                                                            \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "lock_preempted_re_schedule"]
                                    /\ UNCHANGED << queue, lock_info, 
                                                    lock_future, 
                                                    lock_scheduler, 
                                                    lock_PREEMPTED_TASKS, 
                                                    lock_NEXT_TASK, 
                                                    lock_result_context, 
                                                    in_queue, need_sched, 
                                                    state, result_next, 
                                                    result_future, 
                                                    result_context, 
                                                    result_thread, RUNNING, 
                                                    THREADS_pooled, 
                                                    THREAD_POOL, 
                                                    PREEMPTED_TASKS, NEXT_TASK, 
                                                    thread_index, 
                                                    thread_is_new, stored_ctx, 
                                                    stored_task, 
                                                    thread_to_task, 
                                                    task_to_thread, exec_state, 
                                                    preemption_num, wake_other, 
                                                    task_w, task_wa, pid_, 
                                                    head_, pid_s, head, pid_g, 
                                                    pid_w, task_, pid_m, 
                                                    thread, pid_t, ctx, pid_se, 
                                                    next_ctx_s, pid_y, 
                                                    next_ctx, current_ctx_, 
                                                    pid_yi, task_y, 
                                                    next_thread, current_ctx, 
                                                    pid_ru, task_r, next_ctx_, 
                                                    pid_f, task_f, pid, 
                                                    current_task, next_task, 
                                                    next_thread_, task >>

end_yield_and_pool(self) == /\ pc[self] = "end_yield_and_pool"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ current_ctx_' = [current_ctx_ EXCEPT ![self] = Head(stack[self]).current_ctx_]
                            /\ pid_y' = [pid_y EXCEPT ![self] = Head(stack[self]).pid_y]
                            /\ next_ctx' = [next_ctx EXCEPT ![self] = Head(stack[self]).next_ctx]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, state, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREADS_running, 
                                            THREAD_POOL, PREEMPTED_TASKS, 
                                            NEXT_TASK, thread_index, 
                                            thread_is_new, stored_ctx, 
                                            stored_task, thread_to_task, 
                                            task_to_thread, exec_state, 
                                            preemption_num, wake_other, task_w, 
                                            task_wa, pid_, head_, pid_s, head, 
                                            pid_g, pid_w, task_, pid_m, thread, 
                                            pid_r, pid_t, ctx, pid_se, 
                                            next_ctx_s, pid_yi, task_y, 
                                            next_thread, current_ctx, pid_ru, 
                                            task_r, next_ctx_, pid_f, task_f, 
                                            pid, current_task, next_task, 
                                            next_thread_, task >>

yield_and_pool(self) == start_yield_and_pool(self)
                           \/ lock_result_yield_and_pool(self)
                           \/ unlock_result_yield_and_pool(self)
                           \/ context_switch_yield_and_pool(self)
                           \/ re_schedule_yield_and_pool(self)
                           \/ end_yield_and_pool(self)

start_yield_preempted_and_wake_task(self) == /\ pc[self] = "start_yield_preempted_and_wake_task"
                                             /\ IF exec_state[pid_yi[self]] = "Init"
                                                   THEN /\ pc' = [pc EXCEPT ![self] = "lock_result_yield_preempted_and_wake_task"]
                                                        /\ UNCHANGED << exec_state, 
                                                                        task_y, 
                                                                        current_ctx >>
                                                   ELSE /\ IF exec_state[pid_yi[self]] = "Preempted"
                                                              THEN /\ exec_state' = [exec_state EXCEPT ![pid_yi[self]] = "Init"]
                                                                   /\ current_ctx' = [current_ctx EXCEPT ![self] = stored_ctx[pid_yi[self]]]
                                                                   /\ task_y' = [task_y EXCEPT ![self] = stored_task]
                                                                   /\ pc' = [pc EXCEPT ![self] = "re_schedule_yield_preempted_and_wake_task"]
                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "lock_result_yield_preempted_and_wake_task"]
                                                                   /\ UNCHANGED << exec_state, 
                                                                                   task_y, 
                                                                                   current_ctx >>
                                             /\ UNCHANGED << queue, lock_info, 
                                                             lock_future, 
                                                             lock_scheduler, 
                                                             lock_PREEMPTED_TASKS, 
                                                             lock_NEXT_TASK, 
                                                             lock_result_context, 
                                                             in_queue, 
                                                             need_sched, state, 
                                                             result_next, 
                                                             result_future, 
                                                             result_context, 
                                                             result_thread, 
                                                             RUNNING, 
                                                             THREADS_pooled, 
                                                             THREADS_running, 
                                                             THREAD_POOL, 
                                                             PREEMPTED_TASKS, 
                                                             NEXT_TASK, 
                                                             thread_index, 
                                                             thread_is_new, 
                                                             stored_ctx, 
                                                             stored_task, 
                                                             thread_to_task, 
                                                             task_to_thread, 
                                                             preemption_num, 
                                                             wake_other, stack, 
                                                             task_w, task_wa, 
                                                             pid_, head_, 
                                                             pid_s, head, 
                                                             pid_g, pid_w, 
                                                             task_, pid_m, 
                                                             thread, pid_r, 
                                                             pid_t, ctx, 
                                                             pid_se, 
                                                             next_ctx_s, pid_y, 
                                                             next_ctx, 
                                                             current_ctx_, 
                                                             pid_yi, 
                                                             next_thread, 
                                                             pid_ru, task_r, 
                                                             next_ctx_, pid_f, 
                                                             task_f, pid, 
                                                             current_task, 
                                                             next_task, 
                                                             next_thread_, 
                                                             task >>

lock_result_yield_preempted_and_wake_task(self) == /\ pc[self] = "lock_result_yield_preempted_and_wake_task"
                                                   /\ ~lock_result_context
                                                   /\ lock_result_context' = TRUE
                                                   /\ result_context' = THREADS_running[pid_yi[self]]
                                                   /\ THREADS_running' = [THREADS_running EXCEPT ![pid_yi[self]] = -1]
                                                   /\ pc' = [pc EXCEPT ![self] = "unlock_result_yield_preempted_and_wake_task"]
                                                   /\ UNCHANGED << queue, 
                                                                   lock_info, 
                                                                   lock_future, 
                                                                   lock_scheduler, 
                                                                   lock_PREEMPTED_TASKS, 
                                                                   lock_NEXT_TASK, 
                                                                   in_queue, 
                                                                   need_sched, 
                                                                   state, 
                                                                   result_next, 
                                                                   result_future, 
                                                                   result_thread, 
                                                                   RUNNING, 
                                                                   THREADS_pooled, 
                                                                   THREAD_POOL, 
                                                                   PREEMPTED_TASKS, 
                                                                   NEXT_TASK, 
                                                                   thread_index, 
                                                                   thread_is_new, 
                                                                   stored_ctx, 
                                                                   stored_task, 
                                                                   thread_to_task, 
                                                                   task_to_thread, 
                                                                   exec_state, 
                                                                   preemption_num, 
                                                                   wake_other, 
                                                                   stack, 
                                                                   task_w, 
                                                                   task_wa, 
                                                                   pid_, head_, 
                                                                   pid_s, head, 
                                                                   pid_g, 
                                                                   pid_w, 
                                                                   task_, 
                                                                   pid_m, 
                                                                   thread, 
                                                                   pid_r, 
                                                                   pid_t, ctx, 
                                                                   pid_se, 
                                                                   next_ctx_s, 
                                                                   pid_y, 
                                                                   next_ctx, 
                                                                   current_ctx_, 
                                                                   pid_yi, 
                                                                   task_y, 
                                                                   next_thread, 
                                                                   current_ctx, 
                                                                   pid_ru, 
                                                                   task_r, 
                                                                   next_ctx_, 
                                                                   pid_f, 
                                                                   task_f, pid, 
                                                                   current_task, 
                                                                   next_task, 
                                                                   next_thread_, 
                                                                   task >>

unlock_result_yield_preempted_and_wake_task(self) == /\ pc[self] = "unlock_result_yield_preempted_and_wake_task"
                                                     /\ current_ctx' = [current_ctx EXCEPT ![self] = result_context]
                                                     /\ lock_result_context' = FALSE
                                                     /\ pc' = [pc EXCEPT ![self] = "lock_task_yield_preempted_and_wake_task"]
                                                     /\ UNCHANGED << queue, 
                                                                     lock_info, 
                                                                     lock_future, 
                                                                     lock_scheduler, 
                                                                     lock_PREEMPTED_TASKS, 
                                                                     lock_NEXT_TASK, 
                                                                     in_queue, 
                                                                     need_sched, 
                                                                     state, 
                                                                     result_next, 
                                                                     result_future, 
                                                                     result_context, 
                                                                     result_thread, 
                                                                     RUNNING, 
                                                                     THREADS_pooled, 
                                                                     THREADS_running, 
                                                                     THREAD_POOL, 
                                                                     PREEMPTED_TASKS, 
                                                                     NEXT_TASK, 
                                                                     thread_index, 
                                                                     thread_is_new, 
                                                                     stored_ctx, 
                                                                     stored_task, 
                                                                     thread_to_task, 
                                                                     task_to_thread, 
                                                                     exec_state, 
                                                                     preemption_num, 
                                                                     wake_other, 
                                                                     stack, 
                                                                     task_w, 
                                                                     task_wa, 
                                                                     pid_, 
                                                                     head_, 
                                                                     pid_s, 
                                                                     head, 
                                                                     pid_g, 
                                                                     pid_w, 
                                                                     task_, 
                                                                     pid_m, 
                                                                     thread, 
                                                                     pid_r, 
                                                                     pid_t, 
                                                                     ctx, 
                                                                     pid_se, 
                                                                     next_ctx_s, 
                                                                     pid_y, 
                                                                     next_ctx, 
                                                                     current_ctx_, 
                                                                     pid_yi, 
                                                                     task_y, 
                                                                     next_thread, 
                                                                     pid_ru, 
                                                                     task_r, 
                                                                     next_ctx_, 
                                                                     pid_f, 
                                                                     task_f, 
                                                                     pid, 
                                                                     current_task, 
                                                                     next_task, 
                                                                     next_thread_, 
                                                                     task >>

lock_task_yield_preempted_and_wake_task(self) == /\ pc[self] = "lock_task_yield_preempted_and_wake_task"
                                                 /\ ~lock_info[task_y[self]]
                                                 /\ lock_info' = [lock_info EXCEPT ![task_y[self]] = TRUE]
                                                 /\ pc' = [pc EXCEPT ![self] = "set_preempted_yield_preempted_and_wake_task"]
                                                 /\ UNCHANGED << queue, 
                                                                 lock_future, 
                                                                 lock_scheduler, 
                                                                 lock_PREEMPTED_TASKS, 
                                                                 lock_NEXT_TASK, 
                                                                 lock_result_context, 
                                                                 in_queue, 
                                                                 need_sched, 
                                                                 state, 
                                                                 result_next, 
                                                                 result_future, 
                                                                 result_context, 
                                                                 result_thread, 
                                                                 RUNNING, 
                                                                 THREADS_pooled, 
                                                                 THREADS_running, 
                                                                 THREAD_POOL, 
                                                                 PREEMPTED_TASKS, 
                                                                 NEXT_TASK, 
                                                                 thread_index, 
                                                                 thread_is_new, 
                                                                 stored_ctx, 
                                                                 stored_task, 
                                                                 thread_to_task, 
                                                                 task_to_thread, 
                                                                 exec_state, 
                                                                 preemption_num, 
                                                                 wake_other, 
                                                                 stack, task_w, 
                                                                 task_wa, pid_, 
                                                                 head_, pid_s, 
                                                                 head, pid_g, 
                                                                 pid_w, task_, 
                                                                 pid_m, thread, 
                                                                 pid_r, pid_t, 
                                                                 ctx, pid_se, 
                                                                 next_ctx_s, 
                                                                 pid_y, 
                                                                 next_ctx, 
                                                                 current_ctx_, 
                                                                 pid_yi, 
                                                                 task_y, 
                                                                 next_thread, 
                                                                 current_ctx, 
                                                                 pid_ru, 
                                                                 task_r, 
                                                                 next_ctx_, 
                                                                 pid_f, task_f, 
                                                                 pid, 
                                                                 current_task, 
                                                                 next_task, 
                                                                 next_thread_, 
                                                                 task >>

set_preempted_yield_preempted_and_wake_task(self) == /\ pc[self] = "set_preempted_yield_preempted_and_wake_task"
                                                     /\ task_to_thread' = [task_to_thread EXCEPT ![task_y[self]] = current_ctx[self]]
                                                     /\ thread_to_task' = [thread_to_task EXCEPT ![current_ctx[self]] = task_y[self]]
                                                     /\ pc' = [pc EXCEPT ![self] = "set_state_yield_preempted_and_wake_task"]
                                                     /\ UNCHANGED << queue, 
                                                                     lock_info, 
                                                                     lock_future, 
                                                                     lock_scheduler, 
                                                                     lock_PREEMPTED_TASKS, 
                                                                     lock_NEXT_TASK, 
                                                                     lock_result_context, 
                                                                     in_queue, 
                                                                     need_sched, 
                                                                     state, 
                                                                     result_next, 
                                                                     result_future, 
                                                                     result_context, 
                                                                     result_thread, 
                                                                     RUNNING, 
                                                                     THREADS_pooled, 
                                                                     THREADS_running, 
                                                                     THREAD_POOL, 
                                                                     PREEMPTED_TASKS, 
                                                                     NEXT_TASK, 
                                                                     thread_index, 
                                                                     thread_is_new, 
                                                                     stored_ctx, 
                                                                     stored_task, 
                                                                     exec_state, 
                                                                     preemption_num, 
                                                                     wake_other, 
                                                                     stack, 
                                                                     task_w, 
                                                                     task_wa, 
                                                                     pid_, 
                                                                     head_, 
                                                                     pid_s, 
                                                                     head, 
                                                                     pid_g, 
                                                                     pid_w, 
                                                                     task_, 
                                                                     pid_m, 
                                                                     thread, 
                                                                     pid_r, 
                                                                     pid_t, 
                                                                     ctx, 
                                                                     pid_se, 
                                                                     next_ctx_s, 
                                                                     pid_y, 
                                                                     next_ctx, 
                                                                     current_ctx_, 
                                                                     pid_yi, 
                                                                     task_y, 
                                                                     next_thread, 
                                                                     current_ctx, 
                                                                     pid_ru, 
                                                                     task_r, 
                                                                     next_ctx_, 
                                                                     pid_f, 
                                                                     task_f, 
                                                                     pid, 
                                                                     current_task, 
                                                                     next_task, 
                                                                     next_thread_, 
                                                                     task >>

set_state_yield_preempted_and_wake_task(self) == /\ pc[self] = "set_state_yield_preempted_and_wake_task"
                                                 /\ state' = [state EXCEPT ![task_y[self]] = "Preempted"]
                                                 /\ lock_info' = [lock_info EXCEPT ![task_y[self]] = FALSE]
                                                 /\ pc' = [pc EXCEPT ![self] = "lock_preempted_yield_preempted_and_wake_task"]
                                                 /\ UNCHANGED << queue, 
                                                                 lock_future, 
                                                                 lock_scheduler, 
                                                                 lock_PREEMPTED_TASKS, 
                                                                 lock_NEXT_TASK, 
                                                                 lock_result_context, 
                                                                 in_queue, 
                                                                 need_sched, 
                                                                 result_next, 
                                                                 result_future, 
                                                                 result_context, 
                                                                 result_thread, 
                                                                 RUNNING, 
                                                                 THREADS_pooled, 
                                                                 THREADS_running, 
                                                                 THREAD_POOL, 
                                                                 PREEMPTED_TASKS, 
                                                                 NEXT_TASK, 
                                                                 thread_index, 
                                                                 thread_is_new, 
                                                                 stored_ctx, 
                                                                 stored_task, 
                                                                 thread_to_task, 
                                                                 task_to_thread, 
                                                                 exec_state, 
                                                                 preemption_num, 
                                                                 wake_other, 
                                                                 stack, task_w, 
                                                                 task_wa, pid_, 
                                                                 head_, pid_s, 
                                                                 head, pid_g, 
                                                                 pid_w, task_, 
                                                                 pid_m, thread, 
                                                                 pid_r, pid_t, 
                                                                 ctx, pid_se, 
                                                                 next_ctx_s, 
                                                                 pid_y, 
                                                                 next_ctx, 
                                                                 current_ctx_, 
                                                                 pid_yi, 
                                                                 task_y, 
                                                                 next_thread, 
                                                                 current_ctx, 
                                                                 pid_ru, 
                                                                 task_r, 
                                                                 next_ctx_, 
                                                                 pid_f, task_f, 
                                                                 pid, 
                                                                 current_task, 
                                                                 next_task, 
                                                                 next_thread_, 
                                                                 task >>

lock_preempted_yield_preempted_and_wake_task(self) == /\ pc[self] = "lock_preempted_yield_preempted_and_wake_task"
                                                      /\ ~lock_PREEMPTED_TASKS[pid_yi[self]]
                                                      /\ lock_PREEMPTED_TASKS' = [lock_PREEMPTED_TASKS EXCEPT ![pid_yi[self]] = TRUE]
                                                      /\ pc' = [pc EXCEPT ![self] = "push_task_yield_preempted_and_wake_task"]
                                                      /\ UNCHANGED << queue, 
                                                                      lock_info, 
                                                                      lock_future, 
                                                                      lock_scheduler, 
                                                                      lock_NEXT_TASK, 
                                                                      lock_result_context, 
                                                                      in_queue, 
                                                                      need_sched, 
                                                                      state, 
                                                                      result_next, 
                                                                      result_future, 
                                                                      result_context, 
                                                                      result_thread, 
                                                                      RUNNING, 
                                                                      THREADS_pooled, 
                                                                      THREADS_running, 
                                                                      THREAD_POOL, 
                                                                      PREEMPTED_TASKS, 
                                                                      NEXT_TASK, 
                                                                      thread_index, 
                                                                      thread_is_new, 
                                                                      stored_ctx, 
                                                                      stored_task, 
                                                                      thread_to_task, 
                                                                      task_to_thread, 
                                                                      exec_state, 
                                                                      preemption_num, 
                                                                      wake_other, 
                                                                      stack, 
                                                                      task_w, 
                                                                      task_wa, 
                                                                      pid_, 
                                                                      head_, 
                                                                      pid_s, 
                                                                      head, 
                                                                      pid_g, 
                                                                      pid_w, 
                                                                      task_, 
                                                                      pid_m, 
                                                                      thread, 
                                                                      pid_r, 
                                                                      pid_t, 
                                                                      ctx, 
                                                                      pid_se, 
                                                                      next_ctx_s, 
                                                                      pid_y, 
                                                                      next_ctx, 
                                                                      current_ctx_, 
                                                                      pid_yi, 
                                                                      task_y, 
                                                                      next_thread, 
                                                                      current_ctx, 
                                                                      pid_ru, 
                                                                      task_r, 
                                                                      next_ctx_, 
                                                                      pid_f, 
                                                                      task_f, 
                                                                      pid, 
                                                                      current_task, 
                                                                      next_task, 
                                                                      next_thread_, 
                                                                      task >>

push_task_yield_preempted_and_wake_task(self) == /\ pc[self] = "push_task_yield_preempted_and_wake_task"
                                                 /\ PREEMPTED_TASKS' = [PREEMPTED_TASKS EXCEPT ![pid_yi[self]] = <<task_y[self]>> \o PREEMPTED_TASKS[pid_yi[self]]]
                                                 /\ lock_PREEMPTED_TASKS' = [lock_PREEMPTED_TASKS EXCEPT ![pid_yi[self]] = FALSE]
                                                 /\ pc' = [pc EXCEPT ![self] = "context_switch_yield_preempted_and_wake_task"]
                                                 /\ UNCHANGED << queue, 
                                                                 lock_info, 
                                                                 lock_future, 
                                                                 lock_scheduler, 
                                                                 lock_NEXT_TASK, 
                                                                 lock_result_context, 
                                                                 in_queue, 
                                                                 need_sched, 
                                                                 state, 
                                                                 result_next, 
                                                                 result_future, 
                                                                 result_context, 
                                                                 result_thread, 
                                                                 RUNNING, 
                                                                 THREADS_pooled, 
                                                                 THREADS_running, 
                                                                 THREAD_POOL, 
                                                                 NEXT_TASK, 
                                                                 thread_index, 
                                                                 thread_is_new, 
                                                                 stored_ctx, 
                                                                 stored_task, 
                                                                 thread_to_task, 
                                                                 task_to_thread, 
                                                                 exec_state, 
                                                                 preemption_num, 
                                                                 wake_other, 
                                                                 stack, task_w, 
                                                                 task_wa, pid_, 
                                                                 head_, pid_s, 
                                                                 head, pid_g, 
                                                                 pid_w, task_, 
                                                                 pid_m, thread, 
                                                                 pid_r, pid_t, 
                                                                 ctx, pid_se, 
                                                                 next_ctx_s, 
                                                                 pid_y, 
                                                                 next_ctx, 
                                                                 current_ctx_, 
                                                                 pid_yi, 
                                                                 task_y, 
                                                                 next_thread, 
                                                                 current_ctx, 
                                                                 pid_ru, 
                                                                 task_r, 
                                                                 next_ctx_, 
                                                                 pid_f, task_f, 
                                                                 pid, 
                                                                 current_task, 
                                                                 next_task, 
                                                                 next_thread_, 
                                                                 task >>

context_switch_yield_preempted_and_wake_task(self) == /\ pc[self] = "context_switch_yield_preempted_and_wake_task"
                                                      /\ stored_task' = [stored_task EXCEPT ![pid_yi[self]] = thread_to_task[next_thread[self]]]
                                                      /\ stored_ctx' = [stored_ctx EXCEPT ![pid_yi[self]] = next_thread[self]]
                                                      /\ /\ current_ctx' = [current_ctx EXCEPT ![self] = Head(stack[self]).current_ctx]
                                                         /\ next_ctx_s' = [next_ctx_s EXCEPT ![self] = next_thread[self]]
                                                         /\ pid_se' = [pid_se EXCEPT ![self] = pid_yi[self]]
                                                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_exec_state",
                                                                                                  pc        |->  Head(stack[self]).pc,
                                                                                                  pid_se    |->  pid_se[self],
                                                                                                  next_ctx_s |->  next_ctx_s[self] ] >>
                                                                                              \o Tail(stack[self])]
                                                      /\ pc' = [pc EXCEPT ![self] = "start_set_exec_state"]
                                                      /\ UNCHANGED << queue, 
                                                                      lock_info, 
                                                                      lock_future, 
                                                                      lock_scheduler, 
                                                                      lock_PREEMPTED_TASKS, 
                                                                      lock_NEXT_TASK, 
                                                                      lock_result_context, 
                                                                      in_queue, 
                                                                      need_sched, 
                                                                      state, 
                                                                      result_next, 
                                                                      result_future, 
                                                                      result_context, 
                                                                      result_thread, 
                                                                      RUNNING, 
                                                                      THREADS_pooled, 
                                                                      THREADS_running, 
                                                                      THREAD_POOL, 
                                                                      PREEMPTED_TASKS, 
                                                                      NEXT_TASK, 
                                                                      thread_index, 
                                                                      thread_is_new, 
                                                                      thread_to_task, 
                                                                      task_to_thread, 
                                                                      exec_state, 
                                                                      preemption_num, 
                                                                      wake_other, 
                                                                      task_w, 
                                                                      task_wa, 
                                                                      pid_, 
                                                                      head_, 
                                                                      pid_s, 
                                                                      head, 
                                                                      pid_g, 
                                                                      pid_w, 
                                                                      task_, 
                                                                      pid_m, 
                                                                      thread, 
                                                                      pid_r, 
                                                                      pid_t, 
                                                                      ctx, 
                                                                      pid_y, 
                                                                      next_ctx, 
                                                                      current_ctx_, 
                                                                      pid_yi, 
                                                                      task_y, 
                                                                      next_thread, 
                                                                      pid_ru, 
                                                                      task_r, 
                                                                      next_ctx_, 
                                                                      pid_f, 
                                                                      task_f, 
                                                                      pid, 
                                                                      current_task, 
                                                                      next_task, 
                                                                      next_thread_, 
                                                                      task >>

re_schedule_yield_preempted_and_wake_task(self) == /\ pc[self] = "re_schedule_yield_preempted_and_wake_task"
                                                   /\ THREADS_running' = [THREADS_running EXCEPT ![pid_yi[self]] = current_ctx[self]]
                                                   /\ /\ pid_r' = [pid_r EXCEPT ![self] = pid_yi[self]]
                                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "re_schedule",
                                                                                               pc        |->  "end_yield_preempted_and_wake_task",
                                                                                               pid_r     |->  pid_r[self] ] >>
                                                                                           \o stack[self]]
                                                   /\ pc' = [pc EXCEPT ![self] = "lock_preempted_re_schedule"]
                                                   /\ UNCHANGED << queue, 
                                                                   lock_info, 
                                                                   lock_future, 
                                                                   lock_scheduler, 
                                                                   lock_PREEMPTED_TASKS, 
                                                                   lock_NEXT_TASK, 
                                                                   lock_result_context, 
                                                                   in_queue, 
                                                                   need_sched, 
                                                                   state, 
                                                                   result_next, 
                                                                   result_future, 
                                                                   result_context, 
                                                                   result_thread, 
                                                                   RUNNING, 
                                                                   THREADS_pooled, 
                                                                   THREAD_POOL, 
                                                                   PREEMPTED_TASKS, 
                                                                   NEXT_TASK, 
                                                                   thread_index, 
                                                                   thread_is_new, 
                                                                   stored_ctx, 
                                                                   stored_task, 
                                                                   thread_to_task, 
                                                                   task_to_thread, 
                                                                   exec_state, 
                                                                   preemption_num, 
                                                                   wake_other, 
                                                                   task_w, 
                                                                   task_wa, 
                                                                   pid_, head_, 
                                                                   pid_s, head, 
                                                                   pid_g, 
                                                                   pid_w, 
                                                                   task_, 
                                                                   pid_m, 
                                                                   thread, 
                                                                   pid_t, ctx, 
                                                                   pid_se, 
                                                                   next_ctx_s, 
                                                                   pid_y, 
                                                                   next_ctx, 
                                                                   current_ctx_, 
                                                                   pid_yi, 
                                                                   task_y, 
                                                                   next_thread, 
                                                                   current_ctx, 
                                                                   pid_ru, 
                                                                   task_r, 
                                                                   next_ctx_, 
                                                                   pid_f, 
                                                                   task_f, pid, 
                                                                   current_task, 
                                                                   next_task, 
                                                                   next_thread_, 
                                                                   task >>

end_yield_preempted_and_wake_task(self) == /\ pc[self] = "end_yield_preempted_and_wake_task"
                                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                           /\ current_ctx' = [current_ctx EXCEPT ![self] = Head(stack[self]).current_ctx]
                                           /\ pid_yi' = [pid_yi EXCEPT ![self] = Head(stack[self]).pid_yi]
                                           /\ task_y' = [task_y EXCEPT ![self] = Head(stack[self]).task_y]
                                           /\ next_thread' = [next_thread EXCEPT ![self] = Head(stack[self]).next_thread]
                                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                           /\ UNCHANGED << queue, lock_info, 
                                                           lock_future, 
                                                           lock_scheduler, 
                                                           lock_PREEMPTED_TASKS, 
                                                           lock_NEXT_TASK, 
                                                           lock_result_context, 
                                                           in_queue, 
                                                           need_sched, state, 
                                                           result_next, 
                                                           result_future, 
                                                           result_context, 
                                                           result_thread, 
                                                           RUNNING, 
                                                           THREADS_pooled, 
                                                           THREADS_running, 
                                                           THREAD_POOL, 
                                                           PREEMPTED_TASKS, 
                                                           NEXT_TASK, 
                                                           thread_index, 
                                                           thread_is_new, 
                                                           stored_ctx, 
                                                           stored_task, 
                                                           thread_to_task, 
                                                           task_to_thread, 
                                                           exec_state, 
                                                           preemption_num, 
                                                           wake_other, task_w, 
                                                           task_wa, pid_, 
                                                           head_, pid_s, head, 
                                                           pid_g, pid_w, task_, 
                                                           pid_m, thread, 
                                                           pid_r, pid_t, ctx, 
                                                           pid_se, next_ctx_s, 
                                                           pid_y, next_ctx, 
                                                           current_ctx_, 
                                                           pid_ru, task_r, 
                                                           next_ctx_, pid_f, 
                                                           task_f, pid, 
                                                           current_task, 
                                                           next_task, 
                                                           next_thread_, task >>

yield_preempted_and_wake_task(self) == start_yield_preempted_and_wake_task(self)
                                          \/ lock_result_yield_preempted_and_wake_task(self)
                                          \/ unlock_result_yield_preempted_and_wake_task(self)
                                          \/ lock_task_yield_preempted_and_wake_task(self)
                                          \/ set_preempted_yield_preempted_and_wake_task(self)
                                          \/ set_state_yield_preempted_and_wake_task(self)
                                          \/ lock_preempted_yield_preempted_and_wake_task(self)
                                          \/ push_task_yield_preempted_and_wake_task(self)
                                          \/ context_switch_yield_preempted_and_wake_task(self)
                                          \/ re_schedule_yield_preempted_and_wake_task(self)
                                          \/ end_yield_preempted_and_wake_task(self)

start_run_main(self) == /\ pc[self] = "start_run_main"
                        /\ IF exec_state[pid_ru[self]] = "Init"
                              THEN /\ pc' = [pc EXCEPT ![self] = "get_next_run_main"]
                                   /\ UNCHANGED << exec_state, task_r, 
                                                   next_ctx_ >>
                              ELSE /\ IF exec_state[pid_ru[self]] = "Yielded"
                                         THEN /\ task_r' = [task_r EXCEPT ![self] = stored_task[pid_ru[self]]]
                                              /\ next_ctx_' = [next_ctx_ EXCEPT ![self] = stored_ctx[pid_ru[self]]]
                                              /\ pc' = [pc EXCEPT ![self] = "yield_run_main"]
                                              /\ UNCHANGED exec_state
                                         ELSE /\ IF exec_state[pid_ru[self]] = "Preempted"
                                                    THEN /\ task_r' = [task_r EXCEPT ![self] = stored_task[pid_ru[self]]]
                                                         /\ pc' = [pc EXCEPT ![self] = "preempt_after_run_main"]
                                                         /\ UNCHANGED exec_state
                                                    ELSE /\ IF exec_state[pid_ru[self]] = "NotFound"
                                                               THEN /\ exec_state' = [exec_state EXCEPT ![pid_ru[self]] = "Init"]
                                                                    /\ pc' = [pc EXCEPT ![self] = "lock_future2_run_main"]
                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "get_next_run_main"]
                                                                    /\ UNCHANGED exec_state
                                                         /\ UNCHANGED task_r
                                              /\ UNCHANGED next_ctx_
                        /\ UNCHANGED << queue, lock_info, lock_future, 
                                        lock_scheduler, lock_PREEMPTED_TASKS, 
                                        lock_NEXT_TASK, lock_result_context, 
                                        in_queue, need_sched, state, 
                                        result_next, result_future, 
                                        result_context, result_thread, RUNNING, 
                                        THREADS_pooled, THREADS_running, 
                                        THREAD_POOL, PREEMPTED_TASKS, 
                                        NEXT_TASK, thread_index, thread_is_new, 
                                        stored_ctx, stored_task, 
                                        thread_to_task, task_to_thread, 
                                        preemption_num, wake_other, stack, 
                                        task_w, task_wa, pid_, head_, pid_s, 
                                        head, pid_g, pid_w, task_, pid_m, 
                                        thread, pid_r, pid_t, ctx, pid_se, 
                                        next_ctx_s, pid_y, next_ctx, 
                                        current_ctx_, pid_yi, task_y, 
                                        next_thread, current_ctx, pid_ru, 
                                        pid_f, task_f, pid, current_task, 
                                        next_task, next_thread_, task >>

get_next_run_main(self) == /\ pc[self] = "get_next_run_main"
                           /\ /\ pid_g' = [pid_g EXCEPT ![self] = pid_ru[self]]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "get_next_task",
                                                                       pc        |->  "get_task_run_main",
                                                                       pid_g     |->  pid_g[self] ] >>
                                                                   \o stack[self]]
                           /\ pc' = [pc EXCEPT ![self] = "preempt_get_next_task_"]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, thread_is_new, 
                                           stored_ctx, stored_task, 
                                           thread_to_task, task_to_thread, 
                                           exec_state, preemption_num, 
                                           wake_other, task_w, task_wa, pid_, 
                                           head_, pid_s, head, pid_w, task_, 
                                           pid_m, thread, pid_r, pid_t, ctx, 
                                           pid_se, next_ctx_s, pid_y, next_ctx, 
                                           current_ctx_, pid_yi, task_y, 
                                           next_thread, current_ctx, pid_ru, 
                                           task_r, next_ctx_, pid_f, task_f, 
                                           pid, current_task, next_task, 
                                           next_thread_, task >>

get_task_run_main(self) == /\ pc[self] = "get_task_run_main"
                           /\ task_r' = [task_r EXCEPT ![self] = result_next[pid_ru[self]]]
                           /\ IF task_r'[self] < 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "return_run_main"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "lock_task_run_main"]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, thread_is_new, 
                                           stored_ctx, stored_task, 
                                           thread_to_task, task_to_thread, 
                                           exec_state, preemption_num, 
                                           wake_other, stack, task_w, task_wa, 
                                           pid_, head_, pid_s, head, pid_g, 
                                           pid_w, task_, pid_m, thread, pid_r, 
                                           pid_t, ctx, pid_se, next_ctx_s, 
                                           pid_y, next_ctx, current_ctx_, 
                                           pid_yi, task_y, next_thread, 
                                           current_ctx, pid_ru, next_ctx_, 
                                           pid_f, task_f, pid, current_task, 
                                           next_task, next_thread_, task >>

return_run_main(self) == /\ pc[self] = "return_run_main"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ task_r' = [task_r EXCEPT ![self] = Head(stack[self]).task_r]
                         /\ next_ctx_' = [next_ctx_ EXCEPT ![self] = Head(stack[self]).next_ctx_]
                         /\ pid_ru' = [pid_ru EXCEPT ![self] = Head(stack[self]).pid_ru]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << queue, lock_info, lock_future, 
                                         lock_scheduler, lock_PREEMPTED_TASKS, 
                                         lock_NEXT_TASK, lock_result_context, 
                                         in_queue, need_sched, state, 
                                         result_next, result_future, 
                                         result_context, result_thread, 
                                         RUNNING, THREADS_pooled, 
                                         THREADS_running, THREAD_POOL, 
                                         PREEMPTED_TASKS, NEXT_TASK, 
                                         thread_index, thread_is_new, 
                                         stored_ctx, stored_task, 
                                         thread_to_task, task_to_thread, 
                                         exec_state, preemption_num, 
                                         wake_other, task_w, task_wa, pid_, 
                                         head_, pid_s, head, pid_g, pid_w, 
                                         task_, pid_m, thread, pid_r, pid_t, 
                                         ctx, pid_se, next_ctx_s, pid_y, 
                                         next_ctx, current_ctx_, pid_yi, 
                                         task_y, next_thread, current_ctx, 
                                         pid_f, task_f, pid, current_task, 
                                         next_task, next_thread_, task >>

lock_task_run_main(self) == /\ pc[self] = "lock_task_run_main"
                            /\ next_ctx_' = [next_ctx_ EXCEPT ![self] = task_to_thread[task_r[self]]]
                            /\ IF next_ctx_'[self] > 0
                                  THEN /\ state' = [state EXCEPT ![task_r[self]] = "Running"]
                                       /\ pc' = [pc EXCEPT ![self] = "yield_run_main"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "lock_future_run_main"]
                                       /\ state' = state
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREADS_running, 
                                            THREAD_POOL, PREEMPTED_TASKS, 
                                            NEXT_TASK, thread_index, 
                                            thread_is_new, stored_ctx, 
                                            stored_task, thread_to_task, 
                                            task_to_thread, exec_state, 
                                            preemption_num, wake_other, stack, 
                                            task_w, task_wa, pid_, head_, 
                                            pid_s, head, pid_g, pid_w, task_, 
                                            pid_m, thread, pid_r, pid_t, ctx, 
                                            pid_se, next_ctx_s, pid_y, 
                                            next_ctx, current_ctx_, pid_yi, 
                                            task_y, next_thread, current_ctx, 
                                            pid_ru, task_r, pid_f, task_f, pid, 
                                            current_task, next_task, 
                                            next_thread_, task >>

yield_run_main(self) == /\ pc[self] = "yield_run_main"
                        /\ /\ next_ctx' = [next_ctx EXCEPT ![self] = next_ctx_[self]]
                           /\ pid_y' = [pid_y EXCEPT ![self] = pid_ru[self]]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "yield_and_pool",
                                                                    pc        |->  "continue_run_main",
                                                                    current_ctx_ |->  current_ctx_[self],
                                                                    pid_y     |->  pid_y[self],
                                                                    next_ctx  |->  next_ctx[self] ] >>
                                                                \o stack[self]]
                        /\ current_ctx_' = [current_ctx_ EXCEPT ![self] = defaultInitValue]
                        /\ pc' = [pc EXCEPT ![self] = "start_yield_and_pool"]
                        /\ UNCHANGED << queue, lock_info, lock_future, 
                                        lock_scheduler, lock_PREEMPTED_TASKS, 
                                        lock_NEXT_TASK, lock_result_context, 
                                        in_queue, need_sched, state, 
                                        result_next, result_future, 
                                        result_context, result_thread, RUNNING, 
                                        THREADS_pooled, THREADS_running, 
                                        THREAD_POOL, PREEMPTED_TASKS, 
                                        NEXT_TASK, thread_index, thread_is_new, 
                                        stored_ctx, stored_task, 
                                        thread_to_task, task_to_thread, 
                                        exec_state, preemption_num, wake_other, 
                                        task_w, task_wa, pid_, head_, pid_s, 
                                        head, pid_g, pid_w, task_, pid_m, 
                                        thread, pid_r, pid_t, ctx, pid_se, 
                                        next_ctx_s, pid_yi, task_y, 
                                        next_thread, current_ctx, pid_ru, 
                                        task_r, next_ctx_, pid_f, task_f, pid, 
                                        current_task, next_task, next_thread_, 
                                        task >>

continue_run_main(self) == /\ pc[self] = "continue_run_main"
                           /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, thread_is_new, 
                                           stored_ctx, stored_task, 
                                           thread_to_task, task_to_thread, 
                                           exec_state, preemption_num, 
                                           wake_other, stack, task_w, task_wa, 
                                           pid_, head_, pid_s, head, pid_g, 
                                           pid_w, task_, pid_m, thread, pid_r, 
                                           pid_t, ctx, pid_se, next_ctx_s, 
                                           pid_y, next_ctx, current_ctx_, 
                                           pid_yi, task_y, next_thread, 
                                           current_ctx, pid_ru, task_r, 
                                           next_ctx_, pid_f, task_f, pid, 
                                           current_task, next_task, 
                                           next_thread_, task >>

lock_future_run_main(self) == /\ pc[self] = "lock_future_run_main"
                              /\ IF lock_future[task_r[self]]
                                    THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                                     pc        |->  "start_run_main",
                                                                                     task_wa   |->  task_wa[self] ] >>
                                                                                 \o stack[self]]
                                            /\ task_wa' = [task_wa EXCEPT ![self] = task_r[self]]
                                         /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                                         /\ UNCHANGED lock_future
                                    ELSE /\ lock_future' = [lock_future EXCEPT ![task_r[self]] = TRUE]
                                         /\ pc' = [pc EXCEPT ![self] = "check_run_main"]
                                         /\ UNCHANGED << stack, task_wa >>
                              /\ UNCHANGED << queue, lock_info, lock_scheduler, 
                                              lock_PREEMPTED_TASKS, 
                                              lock_NEXT_TASK, 
                                              lock_result_context, in_queue, 
                                              need_sched, state, result_next, 
                                              result_future, result_context, 
                                              result_thread, RUNNING, 
                                              THREADS_pooled, THREADS_running, 
                                              THREAD_POOL, PREEMPTED_TASKS, 
                                              NEXT_TASK, thread_index, 
                                              thread_is_new, stored_ctx, 
                                              stored_task, thread_to_task, 
                                              task_to_thread, exec_state, 
                                              preemption_num, wake_other, 
                                              task_w, pid_, head_, pid_s, head, 
                                              pid_g, pid_w, task_, pid_m, 
                                              thread, pid_r, pid_t, ctx, 
                                              pid_se, next_ctx_s, pid_y, 
                                              next_ctx, current_ctx_, pid_yi, 
                                              task_y, next_thread, current_ctx, 
                                              pid_ru, task_r, next_ctx_, pid_f, 
                                              task_f, pid, current_task, 
                                              next_task, next_thread_, task >>

check_run_main(self) == /\ pc[self] = "check_run_main"
                        /\ ~lock_info[task_r[self]]
                        /\ lock_info' = [lock_info EXCEPT ![task_r[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = "terminated_run_main"]
                        /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                        lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                        lock_result_context, in_queue, 
                                        need_sched, state, result_next, 
                                        result_future, result_context, 
                                        result_thread, RUNNING, THREADS_pooled, 
                                        THREADS_running, THREAD_POOL, 
                                        PREEMPTED_TASKS, NEXT_TASK, 
                                        thread_index, thread_is_new, 
                                        stored_ctx, stored_task, 
                                        thread_to_task, task_to_thread, 
                                        exec_state, preemption_num, wake_other, 
                                        stack, task_w, task_wa, pid_, head_, 
                                        pid_s, head, pid_g, pid_w, task_, 
                                        pid_m, thread, pid_r, pid_t, ctx, 
                                        pid_se, next_ctx_s, pid_y, next_ctx, 
                                        current_ctx_, pid_yi, task_y, 
                                        next_thread, current_ctx, pid_ru, 
                                        task_r, next_ctx_, pid_f, task_f, pid, 
                                        current_task, next_task, next_thread_, 
                                        task >>

terminated_run_main(self) == /\ pc[self] = "terminated_run_main"
                             /\ IF state[task_r[self]] = "Terminated"
                                   THEN /\ lock_info' = [lock_info EXCEPT ![task_r[self]] = FALSE]
                                        /\ lock_future' = [lock_future EXCEPT ![task_r[self]] = FALSE]
                                        /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "pre_future_run_main"]
                                        /\ UNCHANGED << lock_info, lock_future >>
                             /\ UNCHANGED << queue, lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             thread_is_new, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             preemption_num, wake_other, stack, 
                                             task_w, task_wa, pid_, head_, 
                                             pid_s, head, pid_g, pid_w, task_, 
                                             pid_m, thread, pid_r, pid_t, ctx, 
                                             pid_se, next_ctx_s, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, next_ctx_, pid_f, 
                                             task_f, pid, current_task, 
                                             next_task, next_thread_, task >>

pre_future_run_main(self) == /\ pc[self] = "pre_future_run_main"
                             /\ state' = [state EXCEPT ![task_r[self]] = "Running"]
                             /\ need_sched' = [need_sched EXCEPT ![task_r[self]] = FALSE]
                             /\ lock_info' = [lock_info EXCEPT ![task_r[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = "set_task_run_main"]
                             /\ UNCHANGED << queue, lock_future, 
                                             lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             result_next, result_future, 
                                             result_context, result_thread, 
                                             RUNNING, THREADS_pooled, 
                                             THREADS_running, THREAD_POOL, 
                                             PREEMPTED_TASKS, NEXT_TASK, 
                                             thread_index, thread_is_new, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, preemption_num, 
                                             wake_other, stack, task_w, 
                                             task_wa, pid_, head_, pid_s, head, 
                                             pid_g, pid_w, task_, pid_m, 
                                             thread, pid_r, pid_t, ctx, pid_se, 
                                             next_ctx_s, pid_y, next_ctx, 
                                             current_ctx_, pid_yi, task_y, 
                                             next_thread, current_ctx, pid_ru, 
                                             task_r, next_ctx_, pid_f, task_f, 
                                             pid, current_task, next_task, 
                                             next_thread_, task >>

set_task_run_main(self) == /\ pc[self] = "set_task_run_main"
                           /\ RUNNING' = [RUNNING EXCEPT ![pid_ru[self]] = task_r[self]]
                           /\ lock_future' = [lock_future EXCEPT ![task_r[self]] = FALSE]
                           /\ pc' = [pc EXCEPT ![self] = "preempt_run_main"]
                           /\ UNCHANGED << queue, lock_info, lock_scheduler, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           THREADS_pooled, THREADS_running, 
                                           THREAD_POOL, PREEMPTED_TASKS, 
                                           NEXT_TASK, thread_index, 
                                           thread_is_new, stored_ctx, 
                                           stored_task, thread_to_task, 
                                           task_to_thread, exec_state, 
                                           preemption_num, wake_other, stack, 
                                           task_w, task_wa, pid_, head_, pid_s, 
                                           head, pid_g, pid_w, task_, pid_m, 
                                           thread, pid_r, pid_t, ctx, pid_se, 
                                           next_ctx_s, pid_y, next_ctx, 
                                           current_ctx_, pid_yi, task_y, 
                                           next_thread, current_ctx, pid_ru, 
                                           task_r, next_ctx_, pid_f, task_f, 
                                           pid, current_task, next_task, 
                                           next_thread_, task >>

preempt_run_main(self) == /\ pc[self] = "preempt_run_main"
                          /\ IF preemption_num < PREEMPTION_NUM
                                THEN /\ preemption_num' = preemption_num + 1
                                     /\ /\ pid' = [pid EXCEPT ![self] = pid_ru[self]]
                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_preemption",
                                                                                 pc        |->  "continue_run_main3",
                                                                                 current_task |->  current_task[self],
                                                                                 next_task |->  next_task[self],
                                                                                 next_thread_ |->  next_thread_[self],
                                                                                 pid       |->  pid[self] ] >>
                                                                             \o stack[self]]
                                     /\ current_task' = [current_task EXCEPT ![self] = defaultInitValue]
                                     /\ next_task' = [next_task EXCEPT ![self] = defaultInitValue]
                                     /\ next_thread_' = [next_thread_ EXCEPT ![self] = defaultInitValue]
                                     /\ pc' = [pc EXCEPT ![self] = "start_do_preemption"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "lock_future2_run_main"]
                                     /\ UNCHANGED << preemption_num, stack, 
                                                     pid, current_task, 
                                                     next_task, next_thread_ >>
                          /\ UNCHANGED << queue, lock_info, lock_future, 
                                          lock_scheduler, lock_PREEMPTED_TASKS, 
                                          lock_NEXT_TASK, lock_result_context, 
                                          in_queue, need_sched, state, 
                                          result_next, result_future, 
                                          result_context, result_thread, 
                                          RUNNING, THREADS_pooled, 
                                          THREADS_running, THREAD_POOL, 
                                          PREEMPTED_TASKS, NEXT_TASK, 
                                          thread_index, thread_is_new, 
                                          stored_ctx, stored_task, 
                                          thread_to_task, task_to_thread, 
                                          exec_state, wake_other, task_w, 
                                          task_wa, pid_, head_, pid_s, head, 
                                          pid_g, pid_w, task_, pid_m, thread, 
                                          pid_r, pid_t, ctx, pid_se, 
                                          next_ctx_s, pid_y, next_ctx, 
                                          current_ctx_, pid_yi, task_y, 
                                          next_thread, current_ctx, pid_ru, 
                                          task_r, next_ctx_, pid_f, task_f, 
                                          task >>

continue_run_main3(self) == /\ pc[self] = "continue_run_main3"
                            /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, state, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREADS_running, 
                                            THREAD_POOL, PREEMPTED_TASKS, 
                                            NEXT_TASK, thread_index, 
                                            thread_is_new, stored_ctx, 
                                            stored_task, thread_to_task, 
                                            task_to_thread, exec_state, 
                                            preemption_num, wake_other, stack, 
                                            task_w, task_wa, pid_, head_, 
                                            pid_s, head, pid_g, pid_w, task_, 
                                            pid_m, thread, pid_r, pid_t, ctx, 
                                            pid_se, next_ctx_s, pid_y, 
                                            next_ctx, current_ctx_, pid_yi, 
                                            task_y, next_thread, current_ctx, 
                                            pid_ru, task_r, next_ctx_, pid_f, 
                                            task_f, pid, current_task, 
                                            next_task, next_thread_, task >>

preempt_after_run_main(self) == /\ pc[self] = "preempt_after_run_main"
                                /\ /\ pid' = [pid EXCEPT ![self] = pid_ru[self]]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_preemption",
                                                                            pc        |->  "lock_future2_run_main",
                                                                            current_task |->  current_task[self],
                                                                            next_task |->  next_task[self],
                                                                            next_thread_ |->  next_thread_[self],
                                                                            pid       |->  pid[self] ] >>
                                                                        \o stack[self]]
                                /\ current_task' = [current_task EXCEPT ![self] = defaultInitValue]
                                /\ next_task' = [next_task EXCEPT ![self] = defaultInitValue]
                                /\ next_thread_' = [next_thread_ EXCEPT ![self] = defaultInitValue]
                                /\ pc' = [pc EXCEPT ![self] = "start_do_preemption"]
                                /\ UNCHANGED << queue, lock_info, lock_future, 
                                                lock_scheduler, 
                                                lock_PREEMPTED_TASKS, 
                                                lock_NEXT_TASK, 
                                                lock_result_context, in_queue, 
                                                need_sched, state, result_next, 
                                                result_future, result_context, 
                                                result_thread, RUNNING, 
                                                THREADS_pooled, 
                                                THREADS_running, THREAD_POOL, 
                                                PREEMPTED_TASKS, NEXT_TASK, 
                                                thread_index, thread_is_new, 
                                                stored_ctx, stored_task, 
                                                thread_to_task, task_to_thread, 
                                                exec_state, preemption_num, 
                                                wake_other, task_w, task_wa, 
                                                pid_, head_, pid_s, head, 
                                                pid_g, pid_w, task_, pid_m, 
                                                thread, pid_r, pid_t, ctx, 
                                                pid_se, next_ctx_s, pid_y, 
                                                next_ctx, current_ctx_, pid_yi, 
                                                task_y, next_thread, 
                                                current_ctx, pid_ru, task_r, 
                                                next_ctx_, pid_f, task_f, task >>

lock_future2_run_main(self) == /\ pc[self] = "lock_future2_run_main"
                               /\ lock_future' = [lock_future EXCEPT ![task_r[self]] = TRUE]
                               /\ pc' = [pc EXCEPT ![self] = "start_future_run_main"]
                               /\ UNCHANGED << queue, lock_info, 
                                               lock_scheduler, 
                                               lock_PREEMPTED_TASKS, 
                                               lock_NEXT_TASK, 
                                               lock_result_context, in_queue, 
                                               need_sched, state, result_next, 
                                               result_future, result_context, 
                                               result_thread, RUNNING, 
                                               THREADS_pooled, THREADS_running, 
                                               THREAD_POOL, PREEMPTED_TASKS, 
                                               NEXT_TASK, thread_index, 
                                               thread_is_new, stored_ctx, 
                                               stored_task, thread_to_task, 
                                               task_to_thread, exec_state, 
                                               preemption_num, wake_other, 
                                               stack, task_w, task_wa, pid_, 
                                               head_, pid_s, head, pid_g, 
                                               pid_w, task_, pid_m, thread, 
                                               pid_r, pid_t, ctx, pid_se, 
                                               next_ctx_s, pid_y, next_ctx, 
                                               current_ctx_, pid_yi, task_y, 
                                               next_thread, current_ctx, 
                                               pid_ru, task_r, next_ctx_, 
                                               pid_f, task_f, pid, 
                                               current_task, next_task, 
                                               next_thread_, task >>

start_future_run_main(self) == /\ pc[self] = "start_future_run_main"
                               /\ /\ pid_f' = [pid_f EXCEPT ![self] = pid_ru[self]]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "future",
                                                                           pc        |->  "end_future_run_main",
                                                                           pid_f     |->  pid_f[self],
                                                                           task_f    |->  task_f[self] ] >>
                                                                       \o stack[self]]
                                  /\ task_f' = [task_f EXCEPT ![self] = task_r[self]]
                               /\ pc' = [pc EXCEPT ![self] = "start_future"]
                               /\ UNCHANGED << queue, lock_info, lock_future, 
                                               lock_scheduler, 
                                               lock_PREEMPTED_TASKS, 
                                               lock_NEXT_TASK, 
                                               lock_result_context, in_queue, 
                                               need_sched, state, result_next, 
                                               result_future, result_context, 
                                               result_thread, RUNNING, 
                                               THREADS_pooled, THREADS_running, 
                                               THREAD_POOL, PREEMPTED_TASKS, 
                                               NEXT_TASK, thread_index, 
                                               thread_is_new, stored_ctx, 
                                               stored_task, thread_to_task, 
                                               task_to_thread, exec_state, 
                                               preemption_num, wake_other, 
                                               task_w, task_wa, pid_, head_, 
                                               pid_s, head, pid_g, pid_w, 
                                               task_, pid_m, thread, pid_r, 
                                               pid_t, ctx, pid_se, next_ctx_s, 
                                               pid_y, next_ctx, current_ctx_, 
                                               pid_yi, task_y, next_thread, 
                                               current_ctx, pid_ru, task_r, 
                                               next_ctx_, pid, current_task, 
                                               next_task, next_thread_, task >>

end_future_run_main(self) == /\ pc[self] = "end_future_run_main"
                             /\ lock_future' = [lock_future EXCEPT ![task_r[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = "unset_task_run_main"]
                             /\ UNCHANGED << queue, lock_info, lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             thread_is_new, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             preemption_num, wake_other, stack, 
                                             task_w, task_wa, pid_, head_, 
                                             pid_s, head, pid_g, pid_w, task_, 
                                             pid_m, thread, pid_r, pid_t, ctx, 
                                             pid_se, next_ctx_s, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, next_ctx_, pid_f, 
                                             task_f, pid, current_task, 
                                             next_task, next_thread_, task >>

unset_task_run_main(self) == /\ pc[self] = "unset_task_run_main"
                             /\ RUNNING' = [RUNNING EXCEPT ![pid_ru[self]] = -1]
                             /\ pc' = [pc EXCEPT ![self] = "post_future_run_main"]
                             /\ UNCHANGED << queue, lock_info, lock_future, 
                                             lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, THREADS_pooled, 
                                             THREADS_running, THREAD_POOL, 
                                             PREEMPTED_TASKS, NEXT_TASK, 
                                             thread_index, thread_is_new, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, preemption_num, 
                                             wake_other, stack, task_w, 
                                             task_wa, pid_, head_, pid_s, head, 
                                             pid_g, pid_w, task_, pid_m, 
                                             thread, pid_r, pid_t, ctx, pid_se, 
                                             next_ctx_s, pid_y, next_ctx, 
                                             current_ctx_, pid_yi, task_y, 
                                             next_thread, current_ctx, pid_ru, 
                                             task_r, next_ctx_, pid_f, task_f, 
                                             pid, current_task, next_task, 
                                             next_thread_, task >>

post_future_run_main(self) == /\ pc[self] = "post_future_run_main"
                              /\ ~lock_info[task_r[self]]
                              /\ lock_info' = [lock_info EXCEPT ![task_r[self]] = TRUE]
                              /\ IF result_future[pid_ru[self]] = "Pending"
                                    THEN /\ state' = [state EXCEPT ![task_r[self]] = "Waiting"]
                                         /\ IF need_sched[task_r[self]]
                                               THEN /\ pc' = [pc EXCEPT ![self] = "sched_future_run_main"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "continue_run_main2"]
                                    ELSE /\ IF result_future[pid_ru[self]] = "Ready"
                                               THEN /\ state' = [state EXCEPT ![task_r[self]] = "Terminated"]
                                               ELSE /\ Assert((FALSE), 
                                                              "Failure of assertion at line 538, column 13.")
                                                    /\ state' = state
                                         /\ pc' = [pc EXCEPT ![self] = "continue_run_main2"]
                              /\ UNCHANGED << queue, lock_future, 
                                              lock_scheduler, 
                                              lock_PREEMPTED_TASKS, 
                                              lock_NEXT_TASK, 
                                              lock_result_context, in_queue, 
                                              need_sched, result_next, 
                                              result_future, result_context, 
                                              result_thread, RUNNING, 
                                              THREADS_pooled, THREADS_running, 
                                              THREAD_POOL, PREEMPTED_TASKS, 
                                              NEXT_TASK, thread_index, 
                                              thread_is_new, stored_ctx, 
                                              stored_task, thread_to_task, 
                                              task_to_thread, exec_state, 
                                              preemption_num, wake_other, 
                                              stack, task_w, task_wa, pid_, 
                                              head_, pid_s, head, pid_g, pid_w, 
                                              task_, pid_m, thread, pid_r, 
                                              pid_t, ctx, pid_se, next_ctx_s, 
                                              pid_y, next_ctx, current_ctx_, 
                                              pid_yi, task_y, next_thread, 
                                              current_ctx, pid_ru, task_r, 
                                              next_ctx_, pid_f, task_f, pid, 
                                              current_task, next_task, 
                                              next_thread_, task >>

sched_future_run_main(self) == /\ pc[self] = "sched_future_run_main"
                               /\ need_sched' = [need_sched EXCEPT ![task_r[self]] = FALSE]
                               /\ lock_info' = [lock_info EXCEPT ![task_r[self]] = FALSE]
                               /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                           pc        |->  "start_run_main",
                                                                           task_wa   |->  task_wa[self] ] >>
                                                                       \o stack[self]]
                                  /\ task_wa' = [task_wa EXCEPT ![self] = task_r[self]]
                               /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                               /\ UNCHANGED << queue, lock_future, 
                                               lock_scheduler, 
                                               lock_PREEMPTED_TASKS, 
                                               lock_NEXT_TASK, 
                                               lock_result_context, in_queue, 
                                               state, result_next, 
                                               result_future, result_context, 
                                               result_thread, RUNNING, 
                                               THREADS_pooled, THREADS_running, 
                                               THREAD_POOL, PREEMPTED_TASKS, 
                                               NEXT_TASK, thread_index, 
                                               thread_is_new, stored_ctx, 
                                               stored_task, thread_to_task, 
                                               task_to_thread, exec_state, 
                                               preemption_num, wake_other, 
                                               task_w, pid_, head_, pid_s, 
                                               head, pid_g, pid_w, task_, 
                                               pid_m, thread, pid_r, pid_t, 
                                               ctx, pid_se, next_ctx_s, pid_y, 
                                               next_ctx, current_ctx_, pid_yi, 
                                               task_y, next_thread, 
                                               current_ctx, pid_ru, task_r, 
                                               next_ctx_, pid_f, task_f, pid, 
                                               current_task, next_task, 
                                               next_thread_, task >>

continue_run_main2(self) == /\ pc[self] = "continue_run_main2"
                            /\ lock_info' = [lock_info EXCEPT ![task_r[self]] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                            /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, state, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREADS_running, 
                                            THREAD_POOL, PREEMPTED_TASKS, 
                                            NEXT_TASK, thread_index, 
                                            thread_is_new, stored_ctx, 
                                            stored_task, thread_to_task, 
                                            task_to_thread, exec_state, 
                                            preemption_num, wake_other, stack, 
                                            task_w, task_wa, pid_, head_, 
                                            pid_s, head, pid_g, pid_w, task_, 
                                            pid_m, thread, pid_r, pid_t, ctx, 
                                            pid_se, next_ctx_s, pid_y, 
                                            next_ctx, current_ctx_, pid_yi, 
                                            task_y, next_thread, current_ctx, 
                                            pid_ru, task_r, next_ctx_, pid_f, 
                                            task_f, pid, current_task, 
                                            next_task, next_thread_, task >>

run_main(self) == start_run_main(self) \/ get_next_run_main(self)
                     \/ get_task_run_main(self) \/ return_run_main(self)
                     \/ lock_task_run_main(self) \/ yield_run_main(self)
                     \/ continue_run_main(self)
                     \/ lock_future_run_main(self) \/ check_run_main(self)
                     \/ terminated_run_main(self)
                     \/ pre_future_run_main(self)
                     \/ set_task_run_main(self) \/ preempt_run_main(self)
                     \/ continue_run_main3(self)
                     \/ preempt_after_run_main(self)
                     \/ lock_future2_run_main(self)
                     \/ start_future_run_main(self)
                     \/ end_future_run_main(self)
                     \/ unset_task_run_main(self)
                     \/ post_future_run_main(self)
                     \/ sched_future_run_main(self)
                     \/ continue_run_main2(self)

start_future(self) == /\ pc[self] = "start_future"
                      /\ IF task_f[self] = FUTURE_TASK - 1
                            THEN /\ IF wake_other
                                       THEN /\ result_future' = [result_future EXCEPT ![pid_f[self]] = "Ready"]
                                            /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                                        pc        |->  "end_future",
                                                                                        task_wa   |->  task_wa[self] ] >>
                                                                                    \o stack[self]]
                                               /\ task_wa' = [task_wa EXCEPT ![self] = task_f[self]]
                                            /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                                            /\ UNCHANGED wake_other
                                       ELSE /\ wake_other' = TRUE
                                            /\ result_future' = [result_future EXCEPT ![pid_f[self]] = "Pending"]
                                            /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                                        pc        |->  "end_future",
                                                                                        task_wa   |->  task_wa[self] ] >>
                                                                                    \o stack[self]]
                                               /\ task_wa' = [task_wa EXCEPT ![self] = FUTURE_TASK]
                                            /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                            ELSE /\ IF task_f[self] = FUTURE_TASK
                                       THEN /\ result_future' = [result_future EXCEPT ![pid_f[self]] = "Ready"]
                                            /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake",
                                                                                        pc        |->  "end_future",
                                                                                        task_wa   |->  task_wa[self] ] >>
                                                                                    \o stack[self]]
                                               /\ task_wa' = [task_wa EXCEPT ![self] = FUTURE_TASK - 1]
                                            /\ pc' = [pc EXCEPT ![self] = "start_wake"]
                                       ELSE /\ result_future' = [result_future EXCEPT ![pid_f[self]] = "Ready"]
                                            /\ pc' = [pc EXCEPT ![self] = "end_future"]
                                            /\ UNCHANGED << stack, task_wa >>
                                 /\ UNCHANGED wake_other
                      /\ UNCHANGED << queue, lock_info, lock_future, 
                                      lock_scheduler, lock_PREEMPTED_TASKS, 
                                      lock_NEXT_TASK, lock_result_context, 
                                      in_queue, need_sched, state, result_next, 
                                      result_context, result_thread, RUNNING, 
                                      THREADS_pooled, THREADS_running, 
                                      THREAD_POOL, PREEMPTED_TASKS, NEXT_TASK, 
                                      thread_index, thread_is_new, stored_ctx, 
                                      stored_task, thread_to_task, 
                                      task_to_thread, exec_state, 
                                      preemption_num, task_w, pid_, head_, 
                                      pid_s, head, pid_g, pid_w, task_, pid_m, 
                                      thread, pid_r, pid_t, ctx, pid_se, 
                                      next_ctx_s, pid_y, next_ctx, 
                                      current_ctx_, pid_yi, task_y, 
                                      next_thread, current_ctx, pid_ru, task_r, 
                                      next_ctx_, pid_f, task_f, pid, 
                                      current_task, next_task, next_thread_, 
                                      task >>

end_future(self) == /\ pc[self] = "end_future"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ pid_f' = [pid_f EXCEPT ![self] = Head(stack[self]).pid_f]
                    /\ task_f' = [task_f EXCEPT ![self] = Head(stack[self]).task_f]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << queue, lock_info, lock_future, 
                                    lock_scheduler, lock_PREEMPTED_TASKS, 
                                    lock_NEXT_TASK, lock_result_context, 
                                    in_queue, need_sched, state, result_next, 
                                    result_future, result_context, 
                                    result_thread, RUNNING, THREADS_pooled, 
                                    THREADS_running, THREAD_POOL, 
                                    PREEMPTED_TASKS, NEXT_TASK, thread_index, 
                                    thread_is_new, stored_ctx, stored_task, 
                                    thread_to_task, task_to_thread, exec_state, 
                                    preemption_num, wake_other, task_w, 
                                    task_wa, pid_, head_, pid_s, head, pid_g, 
                                    pid_w, task_, pid_m, thread, pid_r, pid_t, 
                                    ctx, pid_se, next_ctx_s, pid_y, next_ctx, 
                                    current_ctx_, pid_yi, task_y, next_thread, 
                                    current_ctx, pid_ru, task_r, next_ctx_, 
                                    pid, current_task, next_task, next_thread_, 
                                    task >>

future(self) == start_future(self) \/ end_future(self)

start_do_preemption(self) == /\ pc[self] = "start_do_preemption"
                             /\ IF exec_state[pid[self]] = "Init"
                                   THEN /\ pc' = [pc EXCEPT ![self] = "get_current_task_do_preemption"]
                                        /\ UNCHANGED << current_task, 
                                                        next_thread_ >>
                                   ELSE /\ IF exec_state[pid[self]] = "Preempted"
                                              THEN /\ current_task' = [current_task EXCEPT ![self] = stored_task[pid[self]]]
                                                   /\ next_thread_' = [next_thread_ EXCEPT ![self] = stored_ctx[pid[self]]]
                                                   /\ pc' = [pc EXCEPT ![self] = "end_do_preemption"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "get_current_task_do_preemption"]
                                                   /\ UNCHANGED << current_task, 
                                                                   next_thread_ >>
                             /\ UNCHANGED << queue, lock_info, lock_future, 
                                             lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             thread_is_new, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             preemption_num, wake_other, stack, 
                                             task_w, task_wa, pid_, head_, 
                                             pid_s, head, pid_g, pid_w, task_, 
                                             pid_m, thread, pid_r, pid_t, ctx, 
                                             pid_se, next_ctx_s, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, next_ctx_, pid_f, 
                                             task_f, pid, next_task, task >>

get_current_task_do_preemption(self) == /\ pc[self] = "get_current_task_do_preemption"
                                        /\ current_task' = [current_task EXCEPT ![self] = RUNNING[pid[self]]]
                                        /\ IF current_task'[self] < 0
                                              THEN /\ exec_state' = [exec_state EXCEPT ![pid[self]] = "NotFound"]
                                                   /\ pc' = [pc EXCEPT ![self] = "exit_do_preemption1"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "get_next_task_do_preemption"]
                                                   /\ UNCHANGED exec_state
                                        /\ UNCHANGED << queue, lock_info, 
                                                        lock_future, 
                                                        lock_scheduler, 
                                                        lock_PREEMPTED_TASKS, 
                                                        lock_NEXT_TASK, 
                                                        lock_result_context, 
                                                        in_queue, need_sched, 
                                                        state, result_next, 
                                                        result_future, 
                                                        result_context, 
                                                        result_thread, RUNNING, 
                                                        THREADS_pooled, 
                                                        THREADS_running, 
                                                        THREAD_POOL, 
                                                        PREEMPTED_TASKS, 
                                                        NEXT_TASK, 
                                                        thread_index, 
                                                        thread_is_new, 
                                                        stored_ctx, 
                                                        stored_task, 
                                                        thread_to_task, 
                                                        task_to_thread, 
                                                        preemption_num, 
                                                        wake_other, stack, 
                                                        task_w, task_wa, pid_, 
                                                        head_, pid_s, head, 
                                                        pid_g, pid_w, task_, 
                                                        pid_m, thread, pid_r, 
                                                        pid_t, ctx, pid_se, 
                                                        next_ctx_s, pid_y, 
                                                        next_ctx, current_ctx_, 
                                                        pid_yi, task_y, 
                                                        next_thread, 
                                                        current_ctx, pid_ru, 
                                                        task_r, next_ctx_, 
                                                        pid_f, task_f, pid, 
                                                        next_task, 
                                                        next_thread_, task >>

exit_do_preemption1(self) == /\ pc[self] = "exit_do_preemption1"
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ current_task' = [current_task EXCEPT ![self] = Head(stack[self]).current_task]
                             /\ next_task' = [next_task EXCEPT ![self] = Head(stack[self]).next_task]
                             /\ next_thread_' = [next_thread_ EXCEPT ![self] = Head(stack[self]).next_thread_]
                             /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << queue, lock_info, lock_future, 
                                             lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             thread_is_new, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             preemption_num, wake_other, 
                                             task_w, task_wa, pid_, head_, 
                                             pid_s, head, pid_g, pid_w, task_, 
                                             pid_m, thread, pid_r, pid_t, ctx, 
                                             pid_se, next_ctx_s, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, next_ctx_, pid_f, 
                                             task_f, task >>

get_next_task_do_preemption(self) == /\ pc[self] = "get_next_task_do_preemption"
                                     /\ /\ pid_g' = [pid_g EXCEPT ![self] = pid[self]]
                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "get_next_task",
                                                                                 pc        |->  "set_task_do_preemption",
                                                                                 pid_g     |->  pid_g[self] ] >>
                                                                             \o stack[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "preempt_get_next_task_"]
                                     /\ UNCHANGED << queue, lock_info, 
                                                     lock_future, 
                                                     lock_scheduler, 
                                                     lock_PREEMPTED_TASKS, 
                                                     lock_NEXT_TASK, 
                                                     lock_result_context, 
                                                     in_queue, need_sched, 
                                                     state, result_next, 
                                                     result_future, 
                                                     result_context, 
                                                     result_thread, RUNNING, 
                                                     THREADS_pooled, 
                                                     THREADS_running, 
                                                     THREAD_POOL, 
                                                     PREEMPTED_TASKS, 
                                                     NEXT_TASK, thread_index, 
                                                     thread_is_new, stored_ctx, 
                                                     stored_task, 
                                                     thread_to_task, 
                                                     task_to_thread, 
                                                     exec_state, 
                                                     preemption_num, 
                                                     wake_other, task_w, 
                                                     task_wa, pid_, head_, 
                                                     pid_s, head, pid_w, task_, 
                                                     pid_m, thread, pid_r, 
                                                     pid_t, ctx, pid_se, 
                                                     next_ctx_s, pid_y, 
                                                     next_ctx, current_ctx_, 
                                                     pid_yi, task_y, 
                                                     next_thread, current_ctx, 
                                                     pid_ru, task_r, next_ctx_, 
                                                     pid_f, task_f, pid, 
                                                     current_task, next_task, 
                                                     next_thread_, task >>

set_task_do_preemption(self) == /\ pc[self] = "set_task_do_preemption"
                                /\ next_task' = [next_task EXCEPT ![self] = result_next[pid[self]]]
                                /\ IF next_task'[self] < 0
                                      THEN /\ exec_state' = [exec_state EXCEPT ![pid[self]] = "NotFound"]
                                           /\ pc' = [pc EXCEPT ![self] = "exit_do_preemption2"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "lock_task_do_preemption"]
                                           /\ UNCHANGED exec_state
                                /\ UNCHANGED << queue, lock_info, lock_future, 
                                                lock_scheduler, 
                                                lock_PREEMPTED_TASKS, 
                                                lock_NEXT_TASK, 
                                                lock_result_context, in_queue, 
                                                need_sched, state, result_next, 
                                                result_future, result_context, 
                                                result_thread, RUNNING, 
                                                THREADS_pooled, 
                                                THREADS_running, THREAD_POOL, 
                                                PREEMPTED_TASKS, NEXT_TASK, 
                                                thread_index, thread_is_new, 
                                                stored_ctx, stored_task, 
                                                thread_to_task, task_to_thread, 
                                                preemption_num, wake_other, 
                                                stack, task_w, task_wa, pid_, 
                                                head_, pid_s, head, pid_g, 
                                                pid_w, task_, pid_m, thread, 
                                                pid_r, pid_t, ctx, pid_se, 
                                                next_ctx_s, pid_y, next_ctx, 
                                                current_ctx_, pid_yi, task_y, 
                                                next_thread, current_ctx, 
                                                pid_ru, task_r, next_ctx_, 
                                                pid_f, task_f, pid, 
                                                current_task, next_thread_, 
                                                task >>

exit_do_preemption2(self) == /\ pc[self] = "exit_do_preemption2"
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ current_task' = [current_task EXCEPT ![self] = Head(stack[self]).current_task]
                             /\ next_task' = [next_task EXCEPT ![self] = Head(stack[self]).next_task]
                             /\ next_thread_' = [next_thread_ EXCEPT ![self] = Head(stack[self]).next_thread_]
                             /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << queue, lock_info, lock_future, 
                                             lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             thread_is_new, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             preemption_num, wake_other, 
                                             task_w, task_wa, pid_, head_, 
                                             pid_s, head, pid_g, pid_w, task_, 
                                             pid_m, thread, pid_r, pid_t, ctx, 
                                             pid_se, next_ctx_s, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, next_ctx_, pid_f, 
                                             task_f, task >>

lock_task_do_preemption(self) == /\ pc[self] = "lock_task_do_preemption"
                                 /\ ~lock_info[next_task[self]]
                                 /\ lock_info' = [lock_info EXCEPT ![next_task[self]] = TRUE]
                                 /\ next_thread_' = [next_thread_ EXCEPT ![self] = task_to_thread[next_task[self]]]
                                 /\ pc' = [pc EXCEPT ![self] = "yield_do_preemption"]
                                 /\ UNCHANGED << queue, lock_future, 
                                                 lock_scheduler, 
                                                 lock_PREEMPTED_TASKS, 
                                                 lock_NEXT_TASK, 
                                                 lock_result_context, in_queue, 
                                                 need_sched, state, 
                                                 result_next, result_future, 
                                                 result_context, result_thread, 
                                                 RUNNING, THREADS_pooled, 
                                                 THREADS_running, THREAD_POOL, 
                                                 PREEMPTED_TASKS, NEXT_TASK, 
                                                 thread_index, thread_is_new, 
                                                 stored_ctx, stored_task, 
                                                 thread_to_task, 
                                                 task_to_thread, exec_state, 
                                                 preemption_num, wake_other, 
                                                 stack, task_w, task_wa, pid_, 
                                                 head_, pid_s, head, pid_g, 
                                                 pid_w, task_, pid_m, thread, 
                                                 pid_r, pid_t, ctx, pid_se, 
                                                 next_ctx_s, pid_y, next_ctx, 
                                                 current_ctx_, pid_yi, task_y, 
                                                 next_thread, current_ctx, 
                                                 pid_ru, task_r, next_ctx_, 
                                                 pid_f, task_f, pid, 
                                                 current_task, next_task, task >>

yield_do_preemption(self) == /\ pc[self] = "yield_do_preemption"
                             /\ IF next_thread_[self] > 0
                                   THEN /\ /\ next_thread' = [next_thread EXCEPT ![self] = next_thread_[self]]
                                           /\ pid_yi' = [pid_yi EXCEPT ![self] = pid[self]]
                                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "yield_preempted_and_wake_task",
                                                                                    pc        |->  "exit_do_preemption3",
                                                                                    current_ctx |->  current_ctx[self],
                                                                                    pid_yi    |->  pid_yi[self],
                                                                                    task_y    |->  task_y[self],
                                                                                    next_thread |->  next_thread[self] ] >>
                                                                                \o stack[self]]
                                           /\ task_y' = [task_y EXCEPT ![self] = current_task[self]]
                                        /\ current_ctx' = [current_ctx EXCEPT ![self] = defaultInitValue]
                                        /\ pc' = [pc EXCEPT ![self] = "start_yield_preempted_and_wake_task"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "unlock_task_do_preemption"]
                                        /\ UNCHANGED << stack, pid_yi, task_y, 
                                                        next_thread, 
                                                        current_ctx >>
                             /\ UNCHANGED << queue, lock_info, lock_future, 
                                             lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             thread_is_new, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             preemption_num, wake_other, 
                                             task_w, task_wa, pid_, head_, 
                                             pid_s, head, pid_g, pid_w, task_, 
                                             pid_m, thread, pid_r, pid_t, ctx, 
                                             pid_se, next_ctx_s, pid_y, 
                                             next_ctx, current_ctx_, pid_ru, 
                                             task_r, next_ctx_, pid_f, task_f, 
                                             pid, current_task, next_task, 
                                             next_thread_, task >>

exit_do_preemption3(self) == /\ pc[self] = "exit_do_preemption3"
                             /\ lock_info' = [lock_info EXCEPT ![next_task[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ current_task' = [current_task EXCEPT ![self] = Head(stack[self]).current_task]
                             /\ next_task' = [next_task EXCEPT ![self] = Head(stack[self]).next_task]
                             /\ next_thread_' = [next_thread_ EXCEPT ![self] = Head(stack[self]).next_thread_]
                             /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << queue, lock_future, 
                                             lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             thread_is_new, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             preemption_num, wake_other, 
                                             task_w, task_wa, pid_, head_, 
                                             pid_s, head, pid_g, pid_w, task_, 
                                             pid_m, thread, pid_r, pid_t, ctx, 
                                             pid_se, next_ctx_s, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, next_ctx_, pid_f, 
                                             task_f, task >>

unlock_task_do_preemption(self) == /\ pc[self] = "unlock_task_do_preemption"
                                   /\ lock_info' = [lock_info EXCEPT ![next_task[self]] = FALSE]
                                   /\ IF THREADS_pooled = <<>>
                                         THEN /\ result_thread' = [result_thread EXCEPT ![pid[self]] = -1]
                                              /\ UNCHANGED THREADS_pooled
                                         ELSE /\ result_thread' = [result_thread EXCEPT ![pid[self]] = Head(THREADS_pooled)]
                                              /\ THREADS_pooled' = Tail(THREADS_pooled)
                                   /\ pc' = [pc EXCEPT ![self] = "get_thread_do_preemption"]
                                   /\ UNCHANGED << queue, lock_future, 
                                                   lock_scheduler, 
                                                   lock_PREEMPTED_TASKS, 
                                                   lock_NEXT_TASK, 
                                                   lock_result_context, 
                                                   in_queue, need_sched, state, 
                                                   result_next, result_future, 
                                                   result_context, RUNNING, 
                                                   THREADS_running, 
                                                   THREAD_POOL, 
                                                   PREEMPTED_TASKS, NEXT_TASK, 
                                                   thread_index, thread_is_new, 
                                                   stored_ctx, stored_task, 
                                                   thread_to_task, 
                                                   task_to_thread, exec_state, 
                                                   preemption_num, wake_other, 
                                                   stack, task_w, task_wa, 
                                                   pid_, head_, pid_s, head, 
                                                   pid_g, pid_w, task_, pid_m, 
                                                   thread, pid_r, pid_t, ctx, 
                                                   pid_se, next_ctx_s, pid_y, 
                                                   next_ctx, current_ctx_, 
                                                   pid_yi, task_y, next_thread, 
                                                   current_ctx, pid_ru, task_r, 
                                                   next_ctx_, pid_f, task_f, 
                                                   pid, current_task, 
                                                   next_task, next_thread_, 
                                                   task >>

get_thread_do_preemption(self) == /\ pc[self] = "get_thread_do_preemption"
                                  /\ IF result_thread[pid[self]] < 0
                                        THEN /\ thread_index' = thread_index + 1
                                             /\ result_thread' = [result_thread EXCEPT ![pid[self]] = thread_index']
                                             /\ thread_is_new' = [thread_is_new EXCEPT ![thread_index'] = TRUE]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << result_thread, 
                                                             thread_index, 
                                                             thread_is_new >>
                                  /\ pc' = [pc EXCEPT ![self] = "set_thread_do_preemption"]
                                  /\ UNCHANGED << queue, lock_info, 
                                                  lock_future, lock_scheduler, 
                                                  lock_PREEMPTED_TASKS, 
                                                  lock_NEXT_TASK, 
                                                  lock_result_context, 
                                                  in_queue, need_sched, state, 
                                                  result_next, result_future, 
                                                  result_context, RUNNING, 
                                                  THREADS_pooled, 
                                                  THREADS_running, THREAD_POOL, 
                                                  PREEMPTED_TASKS, NEXT_TASK, 
                                                  stored_ctx, stored_task, 
                                                  thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  preemption_num, wake_other, 
                                                  stack, task_w, task_wa, pid_, 
                                                  head_, pid_s, head, pid_g, 
                                                  pid_w, task_, pid_m, thread, 
                                                  pid_r, pid_t, ctx, pid_se, 
                                                  next_ctx_s, pid_y, next_ctx, 
                                                  current_ctx_, pid_yi, task_y, 
                                                  next_thread, current_ctx, 
                                                  pid_ru, task_r, next_ctx_, 
                                                  pid_f, task_f, pid, 
                                                  current_task, next_task, 
                                                  next_thread_, task >>

set_thread_do_preemption(self) == /\ pc[self] = "set_thread_do_preemption"
                                  /\ next_thread_' = [next_thread_ EXCEPT ![self] = result_thread[pid[self]]]
                                  /\ pc' = [pc EXCEPT ![self] = "wait_NEXT_TASK_do_preemption"]
                                  /\ UNCHANGED << queue, lock_info, 
                                                  lock_future, lock_scheduler, 
                                                  lock_PREEMPTED_TASKS, 
                                                  lock_NEXT_TASK, 
                                                  lock_result_context, 
                                                  in_queue, need_sched, state, 
                                                  result_next, result_future, 
                                                  result_context, 
                                                  result_thread, RUNNING, 
                                                  THREADS_pooled, 
                                                  THREADS_running, THREAD_POOL, 
                                                  PREEMPTED_TASKS, NEXT_TASK, 
                                                  thread_index, thread_is_new, 
                                                  stored_ctx, stored_task, 
                                                  thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  preemption_num, wake_other, 
                                                  stack, task_w, task_wa, pid_, 
                                                  head_, pid_s, head, pid_g, 
                                                  pid_w, task_, pid_m, thread, 
                                                  pid_r, pid_t, ctx, pid_se, 
                                                  next_ctx_s, pid_y, next_ctx, 
                                                  current_ctx_, pid_yi, task_y, 
                                                  next_thread, current_ctx, 
                                                  pid_ru, task_r, next_ctx_, 
                                                  pid_f, task_f, pid, 
                                                  current_task, next_task, 
                                                  task >>

wait_NEXT_TASK_do_preemption(self) == /\ pc[self] = "wait_NEXT_TASK_do_preemption"
                                      /\ ~lock_NEXT_TASK[pid[self]]
                                      /\ lock_NEXT_TASK' = [lock_NEXT_TASK EXCEPT ![pid[self]] = TRUE]
                                      /\ pc' = [pc EXCEPT ![self] = "push_NEXT_TASK_do_preemption"]
                                      /\ UNCHANGED << queue, lock_info, 
                                                      lock_future, 
                                                      lock_scheduler, 
                                                      lock_PREEMPTED_TASKS, 
                                                      lock_result_context, 
                                                      in_queue, need_sched, 
                                                      state, result_next, 
                                                      result_future, 
                                                      result_context, 
                                                      result_thread, RUNNING, 
                                                      THREADS_pooled, 
                                                      THREADS_running, 
                                                      THREAD_POOL, 
                                                      PREEMPTED_TASKS, 
                                                      NEXT_TASK, thread_index, 
                                                      thread_is_new, 
                                                      stored_ctx, stored_task, 
                                                      thread_to_task, 
                                                      task_to_thread, 
                                                      exec_state, 
                                                      preemption_num, 
                                                      wake_other, stack, 
                                                      task_w, task_wa, pid_, 
                                                      head_, pid_s, head, 
                                                      pid_g, pid_w, task_, 
                                                      pid_m, thread, pid_r, 
                                                      pid_t, ctx, pid_se, 
                                                      next_ctx_s, pid_y, 
                                                      next_ctx, current_ctx_, 
                                                      pid_yi, task_y, 
                                                      next_thread, current_ctx, 
                                                      pid_ru, task_r, 
                                                      next_ctx_, pid_f, task_f, 
                                                      pid, current_task, 
                                                      next_task, next_thread_, 
                                                      task >>

push_NEXT_TASK_do_preemption(self) == /\ pc[self] = "push_NEXT_TASK_do_preemption"
                                      /\ NEXT_TASK' = [NEXT_TASK EXCEPT ![pid[self]] = Append(NEXT_TASK[pid[self]], next_task[self])]
                                      /\ lock_NEXT_TASK' = [lock_NEXT_TASK EXCEPT ![pid[self]] = FALSE]
                                      /\ pc' = [pc EXCEPT ![self] = "end_do_preemption"]
                                      /\ UNCHANGED << queue, lock_info, 
                                                      lock_future, 
                                                      lock_scheduler, 
                                                      lock_PREEMPTED_TASKS, 
                                                      lock_result_context, 
                                                      in_queue, need_sched, 
                                                      state, result_next, 
                                                      result_future, 
                                                      result_context, 
                                                      result_thread, RUNNING, 
                                                      THREADS_pooled, 
                                                      THREADS_running, 
                                                      THREAD_POOL, 
                                                      PREEMPTED_TASKS, 
                                                      thread_index, 
                                                      thread_is_new, 
                                                      stored_ctx, stored_task, 
                                                      thread_to_task, 
                                                      task_to_thread, 
                                                      exec_state, 
                                                      preemption_num, 
                                                      wake_other, stack, 
                                                      task_w, task_wa, pid_, 
                                                      head_, pid_s, head, 
                                                      pid_g, pid_w, task_, 
                                                      pid_m, thread, pid_r, 
                                                      pid_t, ctx, pid_se, 
                                                      next_ctx_s, pid_y, 
                                                      next_ctx, current_ctx_, 
                                                      pid_yi, task_y, 
                                                      next_thread, current_ctx, 
                                                      pid_ru, task_r, 
                                                      next_ctx_, pid_f, task_f, 
                                                      pid, current_task, 
                                                      next_task, next_thread_, 
                                                      task >>

end_do_preemption(self) == /\ pc[self] = "end_do_preemption"
                           /\ /\ next_thread' = [next_thread EXCEPT ![self] = next_thread_[self]]
                              /\ pid_yi' = [pid_yi EXCEPT ![self] = pid[self]]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "yield_preempted_and_wake_task",
                                                                       pc        |->  "exit_do_preemption4",
                                                                       current_ctx |->  current_ctx[self],
                                                                       pid_yi    |->  pid_yi[self],
                                                                       task_y    |->  task_y[self],
                                                                       next_thread |->  next_thread[self] ] >>
                                                                   \o stack[self]]
                              /\ task_y' = [task_y EXCEPT ![self] = current_task[self]]
                           /\ current_ctx' = [current_ctx EXCEPT ![self] = defaultInitValue]
                           /\ pc' = [pc EXCEPT ![self] = "start_yield_preempted_and_wake_task"]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, thread_is_new, 
                                           stored_ctx, stored_task, 
                                           thread_to_task, task_to_thread, 
                                           exec_state, preemption_num, 
                                           wake_other, task_w, task_wa, pid_, 
                                           head_, pid_s, head, pid_g, pid_w, 
                                           task_, pid_m, thread, pid_r, pid_t, 
                                           ctx, pid_se, next_ctx_s, pid_y, 
                                           next_ctx, current_ctx_, pid_ru, 
                                           task_r, next_ctx_, pid_f, task_f, 
                                           pid, current_task, next_task, 
                                           next_thread_, task >>

exit_do_preemption4(self) == /\ pc[self] = "exit_do_preemption4"
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ current_task' = [current_task EXCEPT ![self] = Head(stack[self]).current_task]
                             /\ next_task' = [next_task EXCEPT ![self] = Head(stack[self]).next_task]
                             /\ next_thread_' = [next_thread_ EXCEPT ![self] = Head(stack[self]).next_thread_]
                             /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << queue, lock_info, lock_future, 
                                             lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             thread_is_new, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             preemption_num, wake_other, 
                                             task_w, task_wa, pid_, head_, 
                                             pid_s, head, pid_g, pid_w, task_, 
                                             pid_m, thread, pid_r, pid_t, ctx, 
                                             pid_se, next_ctx_s, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, next_ctx_, pid_f, 
                                             task_f, task >>

do_preemption(self) == start_do_preemption(self)
                          \/ get_current_task_do_preemption(self)
                          \/ exit_do_preemption1(self)
                          \/ get_next_task_do_preemption(self)
                          \/ set_task_do_preemption(self)
                          \/ exit_do_preemption2(self)
                          \/ lock_task_do_preemption(self)
                          \/ yield_do_preemption(self)
                          \/ exit_do_preemption3(self)
                          \/ unlock_task_do_preemption(self)
                          \/ get_thread_do_preemption(self)
                          \/ set_thread_do_preemption(self)
                          \/ wait_NEXT_TASK_do_preemption(self)
                          \/ push_NEXT_TASK_do_preemption(self)
                          \/ end_do_preemption(self)
                          \/ exit_do_preemption4(self)

start_wake_task_all(self) == /\ pc[self] = "start_wake_task_all"
                             /\ IF task[self] > TASK_NUM - 1
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
                                             lock_scheduler, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             thread_is_new, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             preemption_num, wake_other, 
                                             task_w, pid_, head_, pid_s, head, 
                                             pid_g, pid_w, task_, pid_m, 
                                             thread, pid_r, pid_t, ctx, pid_se, 
                                             next_ctx_s, pid_y, next_ctx, 
                                             current_ctx_, pid_yi, task_y, 
                                             next_thread, current_ctx, pid_ru, 
                                             task_r, next_ctx_, pid_f, task_f, 
                                             pid, current_task, next_task, 
                                             next_thread_ >>

rec_wake_task_all(self) == /\ pc[self] = "rec_wake_task_all"
                           /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_task_all",
                                                                       pc        |->  "end_wake_task_all",
                                                                       task      |->  task[self] ] >>
                                                                   \o stack[self]]
                              /\ task' = [task EXCEPT ![self] = task[self] + 1]
                           /\ pc' = [pc EXCEPT ![self] = "start_wake_task_all"]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, thread_is_new, 
                                           stored_ctx, stored_task, 
                                           thread_to_task, task_to_thread, 
                                           exec_state, preemption_num, 
                                           wake_other, task_w, task_wa, pid_, 
                                           head_, pid_s, head, pid_g, pid_w, 
                                           task_, pid_m, thread, pid_r, pid_t, 
                                           ctx, pid_se, next_ctx_s, pid_y, 
                                           next_ctx, current_ctx_, pid_yi, 
                                           task_y, next_thread, current_ctx, 
                                           pid_ru, task_r, next_ctx_, pid_f, 
                                           task_f, pid, current_task, 
                                           next_task, next_thread_ >>

end_wake_task_all(self) == /\ pc[self] = "end_wake_task_all"
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, thread_is_new, 
                                           stored_ctx, stored_task, 
                                           thread_to_task, task_to_thread, 
                                           exec_state, preemption_num, 
                                           wake_other, task_w, task_wa, pid_, 
                                           head_, pid_s, head, pid_g, pid_w, 
                                           task_, pid_m, thread, pid_r, pid_t, 
                                           ctx, pid_se, next_ctx_s, pid_y, 
                                           next_ctx, current_ctx_, pid_yi, 
                                           task_y, next_thread, current_ctx, 
                                           pid_ru, task_r, next_ctx_, pid_f, 
                                           task_f, pid, current_task, 
                                           next_task, next_thread_ >>

wake_task_all(self) == start_wake_task_all(self) \/ rec_wake_task_all(self)
                          \/ end_wake_task_all(self)

start_worker(self) == /\ pc[self] = "start_worker"
                      /\ IF self = 1
                            THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_task_all",
                                                                             pc        |->  "preempt_init",
                                                                             task      |->  task[self] ] >>
                                                                         \o stack[self]]
                                    /\ task' = [task EXCEPT ![self] = self]
                                 /\ pc' = [pc EXCEPT ![self] = "start_wake_task_all"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "preempt_init"]
                                 /\ UNCHANGED << stack, task >>
                      /\ UNCHANGED << queue, lock_info, lock_future, 
                                      lock_scheduler, lock_PREEMPTED_TASKS, 
                                      lock_NEXT_TASK, lock_result_context, 
                                      in_queue, need_sched, state, result_next, 
                                      result_future, result_context, 
                                      result_thread, RUNNING, THREADS_pooled, 
                                      THREADS_running, THREAD_POOL, 
                                      PREEMPTED_TASKS, NEXT_TASK, thread_index, 
                                      thread_is_new, stored_ctx, stored_task, 
                                      thread_to_task, task_to_thread, 
                                      exec_state, preemption_num, wake_other, 
                                      task_w, task_wa, pid_, head_, pid_s, 
                                      head, pid_g, pid_w, task_, pid_m, thread, 
                                      pid_r, pid_t, ctx, pid_se, next_ctx_s, 
                                      pid_y, next_ctx, current_ctx_, pid_yi, 
                                      task_y, next_thread, current_ctx, pid_ru, 
                                      task_r, next_ctx_, pid_f, task_f, pid, 
                                      current_task, next_task, next_thread_ >>

preempt_init(self) == /\ pc[self] = "preempt_init"
                      /\ thread_index' = thread_index + 1
                      /\ THREADS_running' = [THREADS_running EXCEPT ![self] = thread_index']
                      /\ pc' = [pc EXCEPT ![self] = "run"]
                      /\ UNCHANGED << queue, lock_info, lock_future, 
                                      lock_scheduler, lock_PREEMPTED_TASKS, 
                                      lock_NEXT_TASK, lock_result_context, 
                                      in_queue, need_sched, state, result_next, 
                                      result_future, result_context, 
                                      result_thread, RUNNING, THREADS_pooled, 
                                      THREAD_POOL, PREEMPTED_TASKS, NEXT_TASK, 
                                      thread_is_new, stored_ctx, stored_task, 
                                      thread_to_task, task_to_thread, 
                                      exec_state, preemption_num, wake_other, 
                                      stack, task_w, task_wa, pid_, head_, 
                                      pid_s, head, pid_g, pid_w, task_, pid_m, 
                                      thread, pid_r, pid_t, ctx, pid_se, 
                                      next_ctx_s, pid_y, next_ctx, 
                                      current_ctx_, pid_yi, task_y, 
                                      next_thread, current_ctx, pid_ru, task_r, 
                                      next_ctx_, pid_f, task_f, pid, 
                                      current_task, next_task, next_thread_, 
                                      task >>

run(self) == /\ pc[self] = "run"
             /\ /\ pid_ru' = [pid_ru EXCEPT ![self] = self]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "run_main",
                                                         pc        |->  "Done",
                                                         task_r    |->  task_r[self],
                                                         next_ctx_ |->  next_ctx_[self],
                                                         pid_ru    |->  pid_ru[self] ] >>
                                                     \o stack[self]]
             /\ task_r' = [task_r EXCEPT ![self] = defaultInitValue]
             /\ next_ctx_' = [next_ctx_ EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
             /\ UNCHANGED << queue, lock_info, lock_future, lock_scheduler, 
                             lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                             lock_result_context, in_queue, need_sched, state, 
                             result_next, result_future, result_context, 
                             result_thread, RUNNING, THREADS_pooled, 
                             THREADS_running, THREAD_POOL, PREEMPTED_TASKS, 
                             NEXT_TASK, thread_index, thread_is_new, 
                             stored_ctx, stored_task, thread_to_task, 
                             task_to_thread, exec_state, preemption_num, 
                             wake_other, task_w, task_wa, pid_, head_, pid_s, 
                             head, pid_g, pid_w, task_, pid_m, thread, pid_r, 
                             pid_t, ctx, pid_se, next_ctx_s, pid_y, next_ctx, 
                             current_ctx_, pid_yi, task_y, next_thread, 
                             current_ctx, pid_f, task_f, pid, current_task, 
                             next_task, next_thread_, task >>

W(self) == start_worker(self) \/ preempt_init(self) \/ run(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ wake_task(self) \/ wake(self)
                               \/ preempt_get_next_task(self)
                               \/ scheduler_get_next(self)
                               \/ get_next_task(self)
                               \/ wake_PREEMPTED_TASKS(self)
                               \/ make_all_threads_pooled(self)
                               \/ re_schedule(self) \/ thread_entry(self)
                               \/ set_exec_state(self)
                               \/ yield_and_pool(self)
                               \/ yield_preempted_and_wake_task(self)
                               \/ run_main(self) \/ future(self)
                               \/ do_preemption(self) \/ wake_task_all(self))
           \/ (\E self \in WORKERS: W(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in WORKERS : /\ WF_vars(W(self))
                                 /\ WF_vars(wake_task_all(self))
                                 /\ WF_vars(run_main(self))
                                 /\ WF_vars(wake_task(self))
                                 /\ WF_vars(wake(self))
                                 /\ WF_vars(preempt_get_next_task(self))
                                 /\ WF_vars(scheduler_get_next(self))
                                 /\ WF_vars(get_next_task(self))
                                 /\ WF_vars(wake_PREEMPTED_TASKS(self))
                                 /\ WF_vars(make_all_threads_pooled(self))
                                 /\ WF_vars(re_schedule(self))
                                 /\ WF_vars(thread_entry(self))
                                 /\ WF_vars(set_exec_state(self))
                                 /\ WF_vars(yield_and_pool(self))
                                 /\ WF_vars(yield_preempted_and_wake_task(self))                                 /\ WF_vars(future(self))
                                 /\ WF_vars(do_preemption(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
