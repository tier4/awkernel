----------------- MODULE preemptive ----------------
EXTENDS TLC, Integers, Sequences

CONSTANTS TASK_NUM, WORKERS

(*--algorithm preemptive

variables
    \* awkernel_async_lib::scheduler::fifo::FIFOData::queue
    queue = <<>>;

    \* lock variables
    lock_info = [x \in 1..TASK_NUM |-> FALSE];
    lock_future = [x \in 1..TASK_NUM |-> FALSE];
    lock_scheduler = FALSE;
    lock_THREADS = FALSE;
    lock_THREAD_POOL = [x \in WORKERS |-> FALSE];
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

    preemption_done = 0;

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
procedure wake(task)
begin
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

\* awkernel_async_lib::task::preempt::thread::take_current_context()
procedure take_current_context(pid) begin
    wait_take_current_context:
        await ~lock_THREADS;
        lock_THREADS := TRUE;
    
    set_take_current_context:
        result_context := THREADS_running[pid];
        THREADS_running[pid] := -1;
        lock_THREADS := FALSE;
        return;
end procedure

\* awkernel_async_lib::task::preempt::thread::set_current_context(ctx)
procedure set_current_context(pid, ctx) begin
    wait_set_current_context:
        await ~lock_THREADS;
        lock_THREADS := TRUE;
    
    set_set_current_context:
        THREADS_running[pid] := ctx;
        lock_THREADS := FALSE;
        return;
end procedure

\* awkernel_async_lib::task::preempt::push_to_thread_pool(ctx)
procedure push_to_thread_pool(pid, ctx) begin
    wait_push_to_thread_pool:
        await ~lock_THREAD_POOL[pid];
        lock_THREAD_POOL[pid] := TRUE;
    
    set_push_to_thread_pool:
        THREAD_POOL[pid] := Append(THREAD_POOL[pid], ctx);
        lock_THREAD_POOL[pid] := FALSE;
        return;
end procedure

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

\* awkernel_async_lib::task::preempt::thread::take_pooled_thread()
procedure take_pooled_thread(pid)
begin
    start_take_pooled_thread:
        await ~lock_THREADS;
        lock_THREADS := TRUE;
    
    end_take_pooled_thread:
        if THREADS_pooled = <<>> then
            result_thread[pid] := -1;
        else
            result_thread[pid] := Head(THREADS_pooled);
            THREADS_pooled := Tail(THREADS_pooled);
        end if;

        lock_THREADS := FALSE;
        return;
end procedure;

\* awkernel_async_lib::task::preempt::thread::make_thread_pooled(thread)
procedure make_thread_pooled(thread) begin
    wait_make_thread_pooled:
        await ~lock_THREADS;
        lock_THREADS := TRUE;
    
    push_make_thread_pooled:
        THREADS_pooled := Append(THREADS_pooled, thread);
        lock_THREADS := FALSE;
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
        call make_thread_pooled(thread);

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
    
    lock_pool_re_schedule:
        await ~lock_THREAD_POOL[pid];
        lock_THREAD_POOL[pid] := TRUE;
    
    pool_re_schedule:
        call make_all_threads_pooled(pid);

    unlock_pool_re_schedule:
        lock_THREAD_POOL[pid] := FALSE;
        return;
end procedure;

\* awkernel_async_lib::task::preempt::thread_entry()
procedure thread_entry(pid, ctx)
begin
    start_thread_entry:
        call set_current_context(pid, ctx);
    
    re_schedule_thread_entry:
        call re_schedule(pid);
    
    end_thread_entry:
        call run_main(pid);
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
            goto set_ctx_yield_and_pool;
        end if;

    lock_result_yield_and_pool:
        await ~lock_result_context;
        lock_result_context := TRUE;
    
    get_ctx_yield_and_pool:
        call take_current_context(pid);
    
    unlock_result_yield_and_pool:
        current_ctx := result_context;
        lock_result_context := FALSE;
    
    push_ctx_yield_and_pool:
        call push_to_thread_pool(pid, current_ctx);
    
    \* context_switch
    context_switch_yield_and_pool:
        stored_task[pid] := thread_to_task[next_ctx];
        stored_ctx[pid] := next_ctx;
        call set_exec_state(pid, next_ctx);
        return;
    
    set_ctx_yield_and_pool:
        call set_current_context(pid, current_ctx);

    re_schedule_yield_and_pool:
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
            goto set_ctx_yield_preempted_and_wake_task;
        end if;

    lock_result_yield_preempted_and_wake_task:
        await ~lock_result_context;
        lock_result_context := TRUE;
    
    get_ctx_yield_preempted_and_wake_task:
        call take_current_context(pid);
    
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
    
    set_ctx_yield_preempted_and_wake_task:
        call set_current_context(pid, current_ctx);

    re_schedule_yield_preempted_and_wake_task:
        call re_schedule(pid);
    
    end_yield_preempted_and_wake_task:
        return;
end procedure;

\* awkernel_async_lib::task::run_main()
procedure run_main(pid)
variables
    task;
begin
    start_run_main:
        if exec_state[pid] = "Init" then
            goto get_next_run_main;
        elsif exec_state[pid] = "Yielded" then
            task := stored_task[pid];
            goto yield_run_main;
        elsif exec_state[pid] = "Preempted" then
            task := stored_task[pid];
            preemption_done := preemption_done - 1;
            goto preempt_run_main;
        end if;
        
    get_next_run_main:
        call get_next_task(pid);
    
    get_task_run_main:
        task := result_next[pid];
        if task < 0 then
            goto start_run_main;
        end if;

    lock_task_run_main:
        await ~lock_info[task];
        lock_info[task] := TRUE;

        if task_to_thread[task] > 0 then
            state[task] := "Running";

            yield_run_main:
                call yield_and_pool(pid, task);

            continue_run_main:
                lock_info[task] := FALSE;
                goto start_run_main;
        end if;
    
    unlock_task_run_main:
        lock_info[task] := FALSE;
    
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

    \* TODO: modify as you want
    \* 現状では、preemptionは全体で1回、future()の前で起こる、としている
    preempt_run_main:
        if preemption_done < 1 then
            preemption_done := preemption_done + 1;
            call do_preemption(pid);

            continue_run_main3:
                if exec_state[pid] = "Preempted" then
                    goto start_run_main;
                end if;
        end if;

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

\* modify as you want
procedure future(pid, task)
begin
    start_future:
        result_future[pid] := "Ready";
        return;
end procedure;

\* awkernel_async_lib::task::preempt::init()
procedure preempt_init(pid) begin
    start_preempt_init:
        thread_index := thread_index + 1;
        call set_current_context(pid, thread_index);
    
    end_preempt_init:
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
        if RUNNING[pid] < 0 then
            exit_do_preemption1: return;
        end if;

    get_next_task_do_preemption:
        call get_next_task(pid);
    
    set_task_do_preemption:
        next_task := result_next[pid];
        if next_task < 0 then
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

    take_thread_do_preemption:
        call take_pooled_thread(pid);

    create_thread_do_preemption:
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
        if task > TASK_NUM then
            return;
        else
            call wake(task);
            rec_wake_task_all: call wake_task_all(task + 1);
        end if;

    end_wake_task_all:
        return;
end procedure;

\* awkernel_async_lib::task::run()
fair+ process W \in WORKERS begin
    start_worker:
        if self = 1 then
            call wake_task_all(self);
        end if;
    
    preempt_init:
        call preempt_init(self);
    
    run:
        call run_main(self);
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "81d860ac" /\ chksum(tla) = "ea978efe")
\* Label preempt_get_next_task of procedure get_next_task at line 187 col 9 changed to preempt_get_next_task_
\* Label scheduler_get_next of procedure get_next_task at line 190 col 9 changed to scheduler_get_next_
\* Label preempt_init of process W at line 700 col 9 changed to preempt_init_
\* Procedure variable head of procedure preempt_get_next_task at line 128 col 5 changed to head_
\* Procedure variable task of procedure wake_PREEMPTED_TASKS at line 238 col 5 changed to task_
\* Procedure variable thread of procedure make_all_threads_pooled at line 289 col 5 changed to thread_
\* Procedure variable current_ctx of procedure yield_and_pool at line 369 col 5 changed to current_ctx_
\* Procedure variable task of procedure run_main at line 476 col 5 changed to task_r
\* Procedure variable next_thread of procedure do_preemption at line 612 col 5 changed to next_thread_
\* Parameter task of procedure wake_task at line 84 col 21 changed to task_w
\* Parameter task of procedure wake at line 102 col 16 changed to task_wa
\* Parameter pid of procedure preempt_get_next_task at line 126 col 33 changed to pid_
\* Parameter pid of procedure scheduler_get_next at line 152 col 30 changed to pid_s
\* Parameter pid of procedure get_next_task at line 185 col 25 changed to pid_g
\* Parameter pid of procedure take_current_context at line 199 col 32 changed to pid_t
\* Parameter pid of procedure set_current_context at line 212 col 31 changed to pid_se
\* Parameter ctx of procedure set_current_context at line 212 col 36 changed to ctx_
\* Parameter pid of procedure push_to_thread_pool at line 224 col 31 changed to pid_p
\* Parameter ctx of procedure push_to_thread_pool at line 224 col 36 changed to ctx_p
\* Parameter pid of procedure wake_PREEMPTED_TASKS at line 236 col 32 changed to pid_w
\* Parameter pid of procedure take_pooled_thread at line 256 col 30 changed to pid_ta
\* Parameter pid of procedure make_all_threads_pooled at line 287 col 35 changed to pid_m
\* Parameter pid of procedure re_schedule at line 307 col 23 changed to pid_r
\* Parameter pid of procedure thread_entry at line 331 col 24 changed to pid_th
\* Parameter pid of procedure set_exec_state at line 344 col 26 changed to pid_set
\* Parameter next_ctx of procedure set_exec_state at line 344 col 31 changed to next_ctx_
\* Parameter pid of procedure yield_and_pool at line 367 col 26 changed to pid_y
\* Parameter pid of procedure yield_preempted_and_wake_task at line 412 col 41 changed to pid_yi
\* Parameter task of procedure yield_preempted_and_wake_task at line 412 col 46 changed to task_y
\* Parameter pid of procedure run_main at line 474 col 20 changed to pid_ru
\* Parameter pid of procedure future at line 590 col 18 changed to pid_f
\* Parameter task of procedure future at line 590 col 23 changed to task_f
\* Parameter pid of procedure preempt_init at line 598 col 24 changed to pid_pr
CONSTANT defaultInitValue
VARIABLES queue, lock_info, lock_future, lock_scheduler, lock_THREADS, 
          lock_THREAD_POOL, lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
          lock_result_context, in_queue, need_sched, state, result_next, 
          result_future, result_context, result_thread, RUNNING, 
          THREADS_pooled, THREADS_running, THREAD_POOL, PREEMPTED_TASKS, 
          NEXT_TASK, thread_index, stored_ctx, stored_task, thread_to_task, 
          task_to_thread, exec_state, thread_is_new, preemption_done, pc, 
          stack

(* define statement *)
eventually_terminate == <> \A x \in 1..TASK_NUM: (state[x] = "Terminated")

VARIABLES task_w, task_wa, pid_, head_, pid_s, head, pid_g, pid_t, pid_se, 
          ctx_, pid_p, ctx_p, pid_w, task_, pid_ta, thread, pid_m, thread_, 
          pid_r, pid_th, ctx, pid_set, next_ctx_, pid_y, next_ctx, 
          current_ctx_, pid_yi, task_y, next_thread, current_ctx, pid_ru, 
          task_r, pid_f, task_f, pid_pr, pid, current_task, next_task, 
          next_thread_, task

vars == << queue, lock_info, lock_future, lock_scheduler, lock_THREADS, 
           lock_THREAD_POOL, lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
           lock_result_context, in_queue, need_sched, state, result_next, 
           result_future, result_context, result_thread, RUNNING, 
           THREADS_pooled, THREADS_running, THREAD_POOL, PREEMPTED_TASKS, 
           NEXT_TASK, thread_index, stored_ctx, stored_task, thread_to_task, 
           task_to_thread, exec_state, thread_is_new, preemption_done, pc, 
           stack, task_w, task_wa, pid_, head_, pid_s, head, pid_g, pid_t, 
           pid_se, ctx_, pid_p, ctx_p, pid_w, task_, pid_ta, thread, pid_m, 
           thread_, pid_r, pid_th, ctx, pid_set, next_ctx_, pid_y, next_ctx, 
           current_ctx_, pid_yi, task_y, next_thread, current_ctx, pid_ru, 
           task_r, pid_f, task_f, pid_pr, pid, current_task, next_task, 
           next_thread_, task >>

ProcSet == (WORKERS)

Init == (* Global variables *)
        /\ queue = <<>>
        /\ lock_info = [x \in 1..TASK_NUM |-> FALSE]
        /\ lock_future = [x \in 1..TASK_NUM |-> FALSE]
        /\ lock_scheduler = FALSE
        /\ lock_THREADS = FALSE
        /\ lock_THREAD_POOL = [x \in WORKERS |-> FALSE]
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
        /\ stored_ctx = [x \in WORKERS |-> -1]
        /\ stored_task = [x \in WORKERS |-> -1]
        /\ thread_to_task = [x \in 1..5 |-> -1]
        /\ task_to_thread = [x \in 1..TASK_NUM |-> -1]
        /\ exec_state = [x \in WORKERS |-> "Init"]
        /\ thread_is_new = [x \in 1..5 |-> FALSE]
        /\ preemption_done = 0
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
        (* Procedure take_current_context *)
        /\ pid_t = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure set_current_context *)
        /\ pid_se = [ self \in ProcSet |-> defaultInitValue]
        /\ ctx_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure push_to_thread_pool *)
        /\ pid_p = [ self \in ProcSet |-> defaultInitValue]
        /\ ctx_p = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure wake_PREEMPTED_TASKS *)
        /\ pid_w = [ self \in ProcSet |-> defaultInitValue]
        /\ task_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure take_pooled_thread *)
        /\ pid_ta = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure make_thread_pooled *)
        /\ thread = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure make_all_threads_pooled *)
        /\ pid_m = [ self \in ProcSet |-> defaultInitValue]
        /\ thread_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure re_schedule *)
        /\ pid_r = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure thread_entry *)
        /\ pid_th = [ self \in ProcSet |-> defaultInitValue]
        /\ ctx = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure set_exec_state *)
        /\ pid_set = [ self \in ProcSet |-> defaultInitValue]
        /\ next_ctx_ = [ self \in ProcSet |-> defaultInitValue]
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
        (* Procedure future *)
        /\ pid_f = [ self \in ProcSet |-> defaultInitValue]
        /\ task_f = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure preempt_init *)
        /\ pid_pr = [ self \in ProcSet |-> defaultInitValue]
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
                                         lock_THREADS, lock_THREAD_POOL, 
                                         lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                         lock_result_context, in_queue, 
                                         need_sched, state, result_next, 
                                         result_future, result_context, 
                                         result_thread, RUNNING, 
                                         THREADS_pooled, THREADS_running, 
                                         THREAD_POOL, PREEMPTED_TASKS, 
                                         NEXT_TASK, thread_index, stored_ctx, 
                                         stored_task, thread_to_task, 
                                         task_to_thread, exec_state, 
                                         thread_is_new, preemption_done, stack, 
                                         task_w, task_wa, pid_, head_, pid_s, 
                                         head, pid_g, pid_t, pid_se, ctx_, 
                                         pid_p, ctx_p, pid_w, task_, pid_ta, 
                                         thread, pid_m, thread_, pid_r, pid_th, 
                                         ctx, pid_set, next_ctx_, pid_y, 
                                         next_ctx, current_ctx_, pid_yi, 
                                         task_y, next_thread, current_ctx, 
                                         pid_ru, task_r, pid_f, task_f, pid_pr, 
                                         pid, current_task, next_task, 
                                         next_thread_, task >>

lock_wake_task(self) == /\ pc[self] = "lock_wake_task"
                        /\ ~lock_info[task_w[self]]
                        /\ lock_info' = [lock_info EXCEPT ![task_w[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = "end_wake_task"]
                        /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                        lock_THREADS, lock_THREAD_POOL, 
                                        lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                        lock_result_context, in_queue, 
                                        need_sched, state, result_next, 
                                        result_future, result_context, 
                                        result_thread, RUNNING, THREADS_pooled, 
                                        THREADS_running, THREAD_POOL, 
                                        PREEMPTED_TASKS, NEXT_TASK, 
                                        thread_index, stored_ctx, stored_task, 
                                        thread_to_task, task_to_thread, 
                                        exec_state, thread_is_new, 
                                        preemption_done, stack, task_w, 
                                        task_wa, pid_, head_, pid_s, head, 
                                        pid_g, pid_t, pid_se, ctx_, pid_p, 
                                        ctx_p, pid_w, task_, pid_ta, thread, 
                                        pid_m, thread_, pid_r, pid_th, ctx, 
                                        pid_set, next_ctx_, pid_y, next_ctx, 
                                        current_ctx_, pid_yi, task_y, 
                                        next_thread, current_ctx, pid_ru, 
                                        task_r, pid_f, task_f, pid_pr, pid, 
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
                       /\ UNCHANGED << lock_future, lock_THREADS, 
                                       lock_THREAD_POOL, lock_PREEMPTED_TASKS, 
                                       lock_NEXT_TASK, lock_result_context, 
                                       need_sched, state, result_next, 
                                       result_future, result_context, 
                                       result_thread, RUNNING, THREADS_pooled, 
                                       THREADS_running, THREAD_POOL, 
                                       PREEMPTED_TASKS, NEXT_TASK, 
                                       thread_index, stored_ctx, stored_task, 
                                       thread_to_task, task_to_thread, 
                                       exec_state, thread_is_new, 
                                       preemption_done, task_wa, pid_, head_, 
                                       pid_s, head, pid_g, pid_t, pid_se, ctx_, 
                                       pid_p, ctx_p, pid_w, task_, pid_ta, 
                                       thread, pid_m, thread_, pid_r, pid_th, 
                                       ctx, pid_set, next_ctx_, pid_y, 
                                       next_ctx, current_ctx_, pid_yi, task_y, 
                                       next_thread, current_ctx, pid_ru, 
                                       task_r, pid_f, task_f, pid_pr, pid, 
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
                                    lock_THREADS, lock_THREAD_POOL, 
                                    lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                    lock_result_context, in_queue, need_sched, 
                                    state, result_next, result_future, 
                                    result_context, result_thread, RUNNING, 
                                    THREADS_pooled, THREADS_running, 
                                    THREAD_POOL, PREEMPTED_TASKS, NEXT_TASK, 
                                    thread_index, stored_ctx, stored_task, 
                                    thread_to_task, task_to_thread, exec_state, 
                                    thread_is_new, preemption_done, stack, 
                                    task_w, task_wa, pid_, head_, pid_s, head, 
                                    pid_g, pid_t, pid_se, ctx_, pid_p, ctx_p, 
                                    pid_w, task_, pid_ta, thread, pid_m, 
                                    thread_, pid_r, pid_th, ctx, pid_set, 
                                    next_ctx_, pid_y, next_ctx, current_ctx_, 
                                    pid_yi, task_y, next_thread, current_ctx, 
                                    pid_ru, task_r, pid_f, task_f, pid_pr, pid, 
                                    current_task, next_task, next_thread_, 
                                    task >>

need_sched_wake(self) == /\ pc[self] = "need_sched_wake"
                         /\ need_sched' = [need_sched EXCEPT ![task_wa[self]] = TRUE]
                         /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = FALSE]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ task_wa' = [task_wa EXCEPT ![self] = Head(stack[self]).task_wa]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                         lock_THREADS, lock_THREAD_POOL, 
                                         lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                         lock_result_context, in_queue, state, 
                                         result_next, result_future, 
                                         result_context, result_thread, 
                                         RUNNING, THREADS_pooled, 
                                         THREADS_running, THREAD_POOL, 
                                         PREEMPTED_TASKS, NEXT_TASK, 
                                         thread_index, stored_ctx, stored_task, 
                                         thread_to_task, task_to_thread, 
                                         exec_state, thread_is_new, 
                                         preemption_done, task_w, pid_, head_, 
                                         pid_s, head, pid_g, pid_t, pid_se, 
                                         ctx_, pid_p, ctx_p, pid_w, task_, 
                                         pid_ta, thread, pid_m, thread_, pid_r, 
                                         pid_th, ctx, pid_set, next_ctx_, 
                                         pid_y, next_ctx, current_ctx_, pid_yi, 
                                         task_y, next_thread, current_ctx, 
                                         pid_ru, task_r, pid_f, task_f, pid_pr, 
                                         pid, current_task, next_task, 
                                         next_thread_, task >>

wake_but_terminated(self) == /\ pc[self] = "wake_but_terminated"
                             /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ task_wa' = [task_wa EXCEPT ![self] = Head(stack[self]).task_wa]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << queue, lock_future, 
                                             lock_scheduler, lock_THREADS, 
                                             lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, thread_is_new, 
                                             preemption_done, task_w, pid_, 
                                             head_, pid_s, head, pid_g, pid_t, 
                                             pid_se, ctx_, pid_p, ctx_p, pid_w, 
                                             task_, pid_ta, thread, pid_m, 
                                             thread_, pid_r, pid_th, ctx, 
                                             pid_set, next_ctx_, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, pid_f, task_f, 
                                             pid_pr, pid, current_task, 
                                             next_task, next_thread_, task >>

end_wake(self) == /\ pc[self] = "end_wake"
                  /\ lock_info' = [lock_info EXCEPT ![task_wa[self]] = FALSE]
                  /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_task",
                                                              pc        |->  Head(stack[self]).pc,
                                                              task_w    |->  task_w[self] ] >>
                                                          \o Tail(stack[self])]
                     /\ task_w' = [task_w EXCEPT ![self] = task_wa[self]]
                  /\ pc' = [pc EXCEPT ![self] = "start_wake_task"]
                  /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                  lock_THREADS, lock_THREAD_POOL, 
                                  lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                  lock_result_context, in_queue, need_sched, 
                                  state, result_next, result_future, 
                                  result_context, result_thread, RUNNING, 
                                  THREADS_pooled, THREADS_running, THREAD_POOL, 
                                  PREEMPTED_TASKS, NEXT_TASK, thread_index, 
                                  stored_ctx, stored_task, thread_to_task, 
                                  task_to_thread, exec_state, thread_is_new, 
                                  preemption_done, task_wa, pid_, head_, pid_s, 
                                  head, pid_g, pid_t, pid_se, ctx_, pid_p, 
                                  ctx_p, pid_w, task_, pid_ta, thread, pid_m, 
                                  thread_, pid_r, pid_th, ctx, pid_set, 
                                  next_ctx_, pid_y, next_ctx, current_ctx_, 
                                  pid_yi, task_y, next_thread, current_ctx, 
                                  pid_ru, task_r, pid_f, task_f, pid_pr, pid, 
                                  current_task, next_task, next_thread_, task >>

wake(self) == start_wake(self) \/ need_sched_wake(self)
                 \/ wake_but_terminated(self) \/ end_wake(self)

start_preempt_get_next_task(self) == /\ pc[self] = "start_preempt_get_next_task"
                                     /\ ~lock_NEXT_TASK[pid_[self]]
                                     /\ lock_NEXT_TASK' = [lock_NEXT_TASK EXCEPT ![pid_[self]] = TRUE]
                                     /\ pc' = [pc EXCEPT ![self] = "check_preempt_get_next_task"]
                                     /\ UNCHANGED << queue, lock_info, 
                                                     lock_future, 
                                                     lock_scheduler, 
                                                     lock_THREADS, 
                                                     lock_THREAD_POOL, 
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
                                                     stored_ctx, stored_task, 
                                                     thread_to_task, 
                                                     task_to_thread, 
                                                     exec_state, thread_is_new, 
                                                     preemption_done, stack, 
                                                     task_w, task_wa, pid_, 
                                                     head_, pid_s, head, pid_g, 
                                                     pid_t, pid_se, ctx_, 
                                                     pid_p, ctx_p, pid_w, 
                                                     task_, pid_ta, thread, 
                                                     pid_m, thread_, pid_r, 
                                                     pid_th, ctx, pid_set, 
                                                     next_ctx_, pid_y, 
                                                     next_ctx, current_ctx_, 
                                                     pid_yi, task_y, 
                                                     next_thread, current_ctx, 
                                                     pid_ru, task_r, pid_f, 
                                                     task_f, pid_pr, pid, 
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
                                                     lock_THREADS, 
                                                     lock_THREAD_POOL, 
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
                                                     stored_ctx, stored_task, 
                                                     thread_to_task, 
                                                     task_to_thread, 
                                                     exec_state, thread_is_new, 
                                                     preemption_done, task_w, 
                                                     task_wa, pid_s, head, 
                                                     pid_g, pid_t, pid_se, 
                                                     ctx_, pid_p, ctx_p, pid_w, 
                                                     task_, pid_ta, thread, 
                                                     pid_m, thread_, pid_r, 
                                                     pid_th, ctx, pid_set, 
                                                     next_ctx_, pid_y, 
                                                     next_ctx, current_ctx_, 
                                                     pid_yi, task_y, 
                                                     next_thread, current_ctx, 
                                                     pid_ru, task_r, pid_f, 
                                                     task_f, pid_pr, pid, 
                                                     current_task, next_task, 
                                                     next_thread_, task >>

pop_preempt_get_next_task(self) == /\ pc[self] = "pop_preempt_get_next_task"
                                   /\ head_' = [head_ EXCEPT ![self] = Head(NEXT_TASK[pid_[self]])]
                                   /\ NEXT_TASK' = [NEXT_TASK EXCEPT ![pid_[self]] = Tail(NEXT_TASK[pid_[self]])]
                                   /\ pc' = [pc EXCEPT ![self] = "end_preempt_get_next_task"]
                                   /\ UNCHANGED << queue, lock_info, 
                                                   lock_future, lock_scheduler, 
                                                   lock_THREADS, 
                                                   lock_THREAD_POOL, 
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
                                                   thread_index, stored_ctx, 
                                                   stored_task, thread_to_task, 
                                                   task_to_thread, exec_state, 
                                                   thread_is_new, 
                                                   preemption_done, stack, 
                                                   task_w, task_wa, pid_, 
                                                   pid_s, head, pid_g, pid_t, 
                                                   pid_se, ctx_, pid_p, ctx_p, 
                                                   pid_w, task_, pid_ta, 
                                                   thread, pid_m, thread_, 
                                                   pid_r, pid_th, ctx, pid_set, 
                                                   next_ctx_, pid_y, next_ctx, 
                                                   current_ctx_, pid_yi, 
                                                   task_y, next_thread, 
                                                   current_ctx, pid_ru, task_r, 
                                                   pid_f, task_f, pid_pr, pid, 
                                                   current_task, next_task, 
                                                   next_thread_, task >>

end_preempt_get_next_task(self) == /\ pc[self] = "end_preempt_get_next_task"
                                   /\ lock_NEXT_TASK' = [lock_NEXT_TASK EXCEPT ![pid_[self]] = FALSE]
                                   /\ result_next' = [result_next EXCEPT ![pid_[self]] = head_[self]]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ head_' = [head_ EXCEPT ![self] = Head(stack[self]).head_]
                                   /\ pid_' = [pid_ EXCEPT ![self] = Head(stack[self]).pid_]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   /\ UNCHANGED << queue, lock_info, 
                                                   lock_future, lock_scheduler, 
                                                   lock_THREADS, 
                                                   lock_THREAD_POOL, 
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
                                                   thread_index, stored_ctx, 
                                                   stored_task, thread_to_task, 
                                                   task_to_thread, exec_state, 
                                                   thread_is_new, 
                                                   preemption_done, task_w, 
                                                   task_wa, pid_s, head, pid_g, 
                                                   pid_t, pid_se, ctx_, pid_p, 
                                                   ctx_p, pid_w, task_, pid_ta, 
                                                   thread, pid_m, thread_, 
                                                   pid_r, pid_th, ctx, pid_set, 
                                                   next_ctx_, pid_y, next_ctx, 
                                                   current_ctx_, pid_yi, 
                                                   task_y, next_thread, 
                                                   current_ctx, pid_ru, task_r, 
                                                   pid_f, task_f, pid_pr, pid, 
                                                   current_task, next_task, 
                                                   next_thread_, task >>

preempt_get_next_task(self) == start_preempt_get_next_task(self)
                                  \/ check_preempt_get_next_task(self)
                                  \/ pop_preempt_get_next_task(self)
                                  \/ end_preempt_get_next_task(self)

lock_scheduler_get_next(self) == /\ pc[self] = "lock_scheduler_get_next"
                                 /\ ~lock_scheduler
                                 /\ lock_scheduler' = TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "check_scheduler_get_next"]
                                 /\ UNCHANGED << queue, lock_info, lock_future, 
                                                 lock_THREADS, 
                                                 lock_THREAD_POOL, 
                                                 lock_PREEMPTED_TASKS, 
                                                 lock_NEXT_TASK, 
                                                 lock_result_context, in_queue, 
                                                 need_sched, state, 
                                                 result_next, result_future, 
                                                 result_context, result_thread, 
                                                 RUNNING, THREADS_pooled, 
                                                 THREADS_running, THREAD_POOL, 
                                                 PREEMPTED_TASKS, NEXT_TASK, 
                                                 thread_index, stored_ctx, 
                                                 stored_task, thread_to_task, 
                                                 task_to_thread, exec_state, 
                                                 thread_is_new, 
                                                 preemption_done, stack, 
                                                 task_w, task_wa, pid_, head_, 
                                                 pid_s, head, pid_g, pid_t, 
                                                 pid_se, ctx_, pid_p, ctx_p, 
                                                 pid_w, task_, pid_ta, thread, 
                                                 pid_m, thread_, pid_r, pid_th, 
                                                 ctx, pid_set, next_ctx_, 
                                                 pid_y, next_ctx, current_ctx_, 
                                                 pid_yi, task_y, next_thread, 
                                                 current_ctx, pid_ru, task_r, 
                                                 pid_f, task_f, pid_pr, pid, 
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
                                                  lock_future, lock_THREADS, 
                                                  lock_THREAD_POOL, 
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
                                                  thread_index, stored_ctx, 
                                                  stored_task, thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  thread_is_new, 
                                                  preemption_done, task_w, 
                                                  task_wa, pid_, head_, pid_g, 
                                                  pid_t, pid_se, ctx_, pid_p, 
                                                  ctx_p, pid_w, task_, pid_ta, 
                                                  thread, pid_m, thread_, 
                                                  pid_r, pid_th, ctx, pid_set, 
                                                  next_ctx_, pid_y, next_ctx, 
                                                  current_ctx_, pid_yi, task_y, 
                                                  next_thread, current_ctx, 
                                                  pid_ru, task_r, pid_f, 
                                                  task_f, pid_pr, pid, 
                                                  current_task, next_task, 
                                                  next_thread_, task >>

pop_scheduler_get_next(self) == /\ pc[self] = "pop_scheduler_get_next"
                                /\ head' = [head EXCEPT ![self] = Head(queue)]
                                /\ queue' = Tail(queue)
                                /\ pc' = [pc EXCEPT ![self] = "wait_scheduler_get_next"]
                                /\ UNCHANGED << lock_info, lock_future, 
                                                lock_scheduler, lock_THREADS, 
                                                lock_THREAD_POOL, 
                                                lock_PREEMPTED_TASKS, 
                                                lock_NEXT_TASK, 
                                                lock_result_context, in_queue, 
                                                need_sched, state, result_next, 
                                                result_future, result_context, 
                                                result_thread, RUNNING, 
                                                THREADS_pooled, 
                                                THREADS_running, THREAD_POOL, 
                                                PREEMPTED_TASKS, NEXT_TASK, 
                                                thread_index, stored_ctx, 
                                                stored_task, thread_to_task, 
                                                task_to_thread, exec_state, 
                                                thread_is_new, preemption_done, 
                                                stack, task_w, task_wa, pid_, 
                                                head_, pid_s, pid_g, pid_t, 
                                                pid_se, ctx_, pid_p, ctx_p, 
                                                pid_w, task_, pid_ta, thread, 
                                                pid_m, thread_, pid_r, pid_th, 
                                                ctx, pid_set, next_ctx_, pid_y, 
                                                next_ctx, current_ctx_, pid_yi, 
                                                task_y, next_thread, 
                                                current_ctx, pid_ru, task_r, 
                                                pid_f, task_f, pid_pr, pid, 
                                                current_task, next_task, 
                                                next_thread_, task >>

wait_scheduler_get_next(self) == /\ pc[self] = "wait_scheduler_get_next"
                                 /\ ~lock_info[head[self]]
                                 /\ lock_info' = [lock_info EXCEPT ![head[self]] = TRUE]
                                 /\ pc' = [pc EXCEPT ![self] = "end_scheduler_get_next"]
                                 /\ UNCHANGED << queue, lock_future, 
                                                 lock_scheduler, lock_THREADS, 
                                                 lock_THREAD_POOL, 
                                                 lock_PREEMPTED_TASKS, 
                                                 lock_NEXT_TASK, 
                                                 lock_result_context, in_queue, 
                                                 need_sched, state, 
                                                 result_next, result_future, 
                                                 result_context, result_thread, 
                                                 RUNNING, THREADS_pooled, 
                                                 THREADS_running, THREAD_POOL, 
                                                 PREEMPTED_TASKS, NEXT_TASK, 
                                                 thread_index, stored_ctx, 
                                                 stored_task, thread_to_task, 
                                                 task_to_thread, exec_state, 
                                                 thread_is_new, 
                                                 preemption_done, stack, 
                                                 task_w, task_wa, pid_, head_, 
                                                 pid_s, head, pid_g, pid_t, 
                                                 pid_se, ctx_, pid_p, ctx_p, 
                                                 pid_w, task_, pid_ta, thread, 
                                                 pid_m, thread_, pid_r, pid_th, 
                                                 ctx, pid_set, next_ctx_, 
                                                 pid_y, next_ctx, current_ctx_, 
                                                 pid_yi, task_y, next_thread, 
                                                 current_ctx, pid_ru, task_r, 
                                                 pid_f, task_f, pid_pr, pid, 
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
                                                lock_THREADS, lock_THREAD_POOL, 
                                                lock_PREEMPTED_TASKS, 
                                                lock_NEXT_TASK, 
                                                lock_result_context, 
                                                need_sched, result_future, 
                                                result_context, result_thread, 
                                                RUNNING, THREADS_pooled, 
                                                THREADS_running, THREAD_POOL, 
                                                PREEMPTED_TASKS, NEXT_TASK, 
                                                thread_index, stored_ctx, 
                                                stored_task, thread_to_task, 
                                                task_to_thread, exec_state, 
                                                thread_is_new, preemption_done, 
                                                task_w, task_wa, pid_, head_, 
                                                pid_g, pid_t, pid_se, ctx_, 
                                                pid_p, ctx_p, pid_w, task_, 
                                                pid_ta, thread, pid_m, thread_, 
                                                pid_r, pid_th, ctx, pid_set, 
                                                next_ctx_, pid_y, next_ctx, 
                                                current_ctx_, pid_yi, task_y, 
                                                next_thread, current_ctx, 
                                                pid_ru, task_r, pid_f, task_f, 
                                                pid_pr, pid, current_task, 
                                                next_task, next_thread_, task >>

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
                                                lock_scheduler, lock_THREADS, 
                                                lock_THREAD_POOL, 
                                                lock_PREEMPTED_TASKS, 
                                                lock_NEXT_TASK, 
                                                lock_result_context, in_queue, 
                                                need_sched, state, result_next, 
                                                result_future, result_context, 
                                                result_thread, RUNNING, 
                                                THREADS_pooled, 
                                                THREADS_running, THREAD_POOL, 
                                                PREEMPTED_TASKS, NEXT_TASK, 
                                                thread_index, stored_ctx, 
                                                stored_task, thread_to_task, 
                                                task_to_thread, exec_state, 
                                                thread_is_new, preemption_done, 
                                                task_w, task_wa, pid_s, head, 
                                                pid_g, pid_t, pid_se, ctx_, 
                                                pid_p, ctx_p, pid_w, task_, 
                                                pid_ta, thread, pid_m, thread_, 
                                                pid_r, pid_th, ctx, pid_set, 
                                                next_ctx_, pid_y, next_ctx, 
                                                current_ctx_, pid_yi, task_y, 
                                                next_thread, current_ctx, 
                                                pid_ru, task_r, pid_f, task_f, 
                                                pid_pr, pid, current_task, 
                                                next_task, next_thread_, task >>

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
                                             lock_scheduler, lock_THREADS, 
                                             lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, thread_is_new, 
                                             preemption_done, task_w, task_wa, 
                                             pid_, head_, pid_g, pid_t, pid_se, 
                                             ctx_, pid_p, ctx_p, pid_w, task_, 
                                             pid_ta, thread, pid_m, thread_, 
                                             pid_r, pid_th, ctx, pid_set, 
                                             next_ctx_, pid_y, next_ctx, 
                                             current_ctx_, pid_yi, task_y, 
                                             next_thread, current_ctx, pid_ru, 
                                             task_r, pid_f, task_f, pid_pr, 
                                             pid, current_task, next_task, 
                                             next_thread_, task >>

end_get_next_task(self) == /\ pc[self] = "end_get_next_task"
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ pid_g' = [pid_g EXCEPT ![self] = Head(stack[self]).pid_g]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, lock_THREADS, 
                                           lock_THREAD_POOL, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, stored_ctx, 
                                           stored_task, thread_to_task, 
                                           task_to_thread, exec_state, 
                                           thread_is_new, preemption_done, 
                                           task_w, task_wa, pid_, head_, pid_s, 
                                           head, pid_t, pid_se, ctx_, pid_p, 
                                           ctx_p, pid_w, task_, pid_ta, thread, 
                                           pid_m, thread_, pid_r, pid_th, ctx, 
                                           pid_set, next_ctx_, pid_y, next_ctx, 
                                           current_ctx_, pid_yi, task_y, 
                                           next_thread, current_ctx, pid_ru, 
                                           task_r, pid_f, task_f, pid_pr, pid, 
                                           current_task, next_task, 
                                           next_thread_, task >>

get_next_task(self) == preempt_get_next_task_(self)
                          \/ scheduler_get_next_(self)
                          \/ end_get_next_task(self)

wait_take_current_context(self) == /\ pc[self] = "wait_take_current_context"
                                   /\ ~lock_THREADS
                                   /\ lock_THREADS' = TRUE
                                   /\ pc' = [pc EXCEPT ![self] = "set_take_current_context"]
                                   /\ UNCHANGED << queue, lock_info, 
                                                   lock_future, lock_scheduler, 
                                                   lock_THREAD_POOL, 
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
                                                   PREEMPTED_TASKS, NEXT_TASK, 
                                                   thread_index, stored_ctx, 
                                                   stored_task, thread_to_task, 
                                                   task_to_thread, exec_state, 
                                                   thread_is_new, 
                                                   preemption_done, stack, 
                                                   task_w, task_wa, pid_, 
                                                   head_, pid_s, head, pid_g, 
                                                   pid_t, pid_se, ctx_, pid_p, 
                                                   ctx_p, pid_w, task_, pid_ta, 
                                                   thread, pid_m, thread_, 
                                                   pid_r, pid_th, ctx, pid_set, 
                                                   next_ctx_, pid_y, next_ctx, 
                                                   current_ctx_, pid_yi, 
                                                   task_y, next_thread, 
                                                   current_ctx, pid_ru, task_r, 
                                                   pid_f, task_f, pid_pr, pid, 
                                                   current_task, next_task, 
                                                   next_thread_, task >>

set_take_current_context(self) == /\ pc[self] = "set_take_current_context"
                                  /\ result_context' = THREADS_running[pid_t[self]]
                                  /\ THREADS_running' = [THREADS_running EXCEPT ![pid_t[self]] = -1]
                                  /\ lock_THREADS' = FALSE
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ pid_t' = [pid_t EXCEPT ![self] = Head(stack[self]).pid_t]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  /\ UNCHANGED << queue, lock_info, 
                                                  lock_future, lock_scheduler, 
                                                  lock_THREAD_POOL, 
                                                  lock_PREEMPTED_TASKS, 
                                                  lock_NEXT_TASK, 
                                                  lock_result_context, 
                                                  in_queue, need_sched, state, 
                                                  result_next, result_future, 
                                                  result_thread, RUNNING, 
                                                  THREADS_pooled, THREAD_POOL, 
                                                  PREEMPTED_TASKS, NEXT_TASK, 
                                                  thread_index, stored_ctx, 
                                                  stored_task, thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  thread_is_new, 
                                                  preemption_done, task_w, 
                                                  task_wa, pid_, head_, pid_s, 
                                                  head, pid_g, pid_se, ctx_, 
                                                  pid_p, ctx_p, pid_w, task_, 
                                                  pid_ta, thread, pid_m, 
                                                  thread_, pid_r, pid_th, ctx, 
                                                  pid_set, next_ctx_, pid_y, 
                                                  next_ctx, current_ctx_, 
                                                  pid_yi, task_y, next_thread, 
                                                  current_ctx, pid_ru, task_r, 
                                                  pid_f, task_f, pid_pr, pid, 
                                                  current_task, next_task, 
                                                  next_thread_, task >>

take_current_context(self) == wait_take_current_context(self)
                                 \/ set_take_current_context(self)

wait_set_current_context(self) == /\ pc[self] = "wait_set_current_context"
                                  /\ ~lock_THREADS
                                  /\ lock_THREADS' = TRUE
                                  /\ pc' = [pc EXCEPT ![self] = "set_set_current_context"]
                                  /\ UNCHANGED << queue, lock_info, 
                                                  lock_future, lock_scheduler, 
                                                  lock_THREAD_POOL, 
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
                                                  thread_index, stored_ctx, 
                                                  stored_task, thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  thread_is_new, 
                                                  preemption_done, stack, 
                                                  task_w, task_wa, pid_, head_, 
                                                  pid_s, head, pid_g, pid_t, 
                                                  pid_se, ctx_, pid_p, ctx_p, 
                                                  pid_w, task_, pid_ta, thread, 
                                                  pid_m, thread_, pid_r, 
                                                  pid_th, ctx, pid_set, 
                                                  next_ctx_, pid_y, next_ctx, 
                                                  current_ctx_, pid_yi, task_y, 
                                                  next_thread, current_ctx, 
                                                  pid_ru, task_r, pid_f, 
                                                  task_f, pid_pr, pid, 
                                                  current_task, next_task, 
                                                  next_thread_, task >>

set_set_current_context(self) == /\ pc[self] = "set_set_current_context"
                                 /\ THREADS_running' = [THREADS_running EXCEPT ![pid_se[self]] = ctx_[self]]
                                 /\ lock_THREADS' = FALSE
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ pid_se' = [pid_se EXCEPT ![self] = Head(stack[self]).pid_se]
                                 /\ ctx_' = [ctx_ EXCEPT ![self] = Head(stack[self]).ctx_]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                 /\ UNCHANGED << queue, lock_info, lock_future, 
                                                 lock_scheduler, 
                                                 lock_THREAD_POOL, 
                                                 lock_PREEMPTED_TASKS, 
                                                 lock_NEXT_TASK, 
                                                 lock_result_context, in_queue, 
                                                 need_sched, state, 
                                                 result_next, result_future, 
                                                 result_context, result_thread, 
                                                 RUNNING, THREADS_pooled, 
                                                 THREAD_POOL, PREEMPTED_TASKS, 
                                                 NEXT_TASK, thread_index, 
                                                 stored_ctx, stored_task, 
                                                 thread_to_task, 
                                                 task_to_thread, exec_state, 
                                                 thread_is_new, 
                                                 preemption_done, task_w, 
                                                 task_wa, pid_, head_, pid_s, 
                                                 head, pid_g, pid_t, pid_p, 
                                                 ctx_p, pid_w, task_, pid_ta, 
                                                 thread, pid_m, thread_, pid_r, 
                                                 pid_th, ctx, pid_set, 
                                                 next_ctx_, pid_y, next_ctx, 
                                                 current_ctx_, pid_yi, task_y, 
                                                 next_thread, current_ctx, 
                                                 pid_ru, task_r, pid_f, task_f, 
                                                 pid_pr, pid, current_task, 
                                                 next_task, next_thread_, task >>

set_current_context(self) == wait_set_current_context(self)
                                \/ set_set_current_context(self)

wait_push_to_thread_pool(self) == /\ pc[self] = "wait_push_to_thread_pool"
                                  /\ ~lock_THREAD_POOL[pid_p[self]]
                                  /\ lock_THREAD_POOL' = [lock_THREAD_POOL EXCEPT ![pid_p[self]] = TRUE]
                                  /\ pc' = [pc EXCEPT ![self] = "set_push_to_thread_pool"]
                                  /\ UNCHANGED << queue, lock_info, 
                                                  lock_future, lock_scheduler, 
                                                  lock_THREADS, 
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
                                                  thread_index, stored_ctx, 
                                                  stored_task, thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  thread_is_new, 
                                                  preemption_done, stack, 
                                                  task_w, task_wa, pid_, head_, 
                                                  pid_s, head, pid_g, pid_t, 
                                                  pid_se, ctx_, pid_p, ctx_p, 
                                                  pid_w, task_, pid_ta, thread, 
                                                  pid_m, thread_, pid_r, 
                                                  pid_th, ctx, pid_set, 
                                                  next_ctx_, pid_y, next_ctx, 
                                                  current_ctx_, pid_yi, task_y, 
                                                  next_thread, current_ctx, 
                                                  pid_ru, task_r, pid_f, 
                                                  task_f, pid_pr, pid, 
                                                  current_task, next_task, 
                                                  next_thread_, task >>

set_push_to_thread_pool(self) == /\ pc[self] = "set_push_to_thread_pool"
                                 /\ THREAD_POOL' = [THREAD_POOL EXCEPT ![pid_p[self]] = Append(THREAD_POOL[pid_p[self]], ctx_p[self])]
                                 /\ lock_THREAD_POOL' = [lock_THREAD_POOL EXCEPT ![pid_p[self]] = FALSE]
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ pid_p' = [pid_p EXCEPT ![self] = Head(stack[self]).pid_p]
                                 /\ ctx_p' = [ctx_p EXCEPT ![self] = Head(stack[self]).ctx_p]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                 /\ UNCHANGED << queue, lock_info, lock_future, 
                                                 lock_scheduler, lock_THREADS, 
                                                 lock_PREEMPTED_TASKS, 
                                                 lock_NEXT_TASK, 
                                                 lock_result_context, in_queue, 
                                                 need_sched, state, 
                                                 result_next, result_future, 
                                                 result_context, result_thread, 
                                                 RUNNING, THREADS_pooled, 
                                                 THREADS_running, 
                                                 PREEMPTED_TASKS, NEXT_TASK, 
                                                 thread_index, stored_ctx, 
                                                 stored_task, thread_to_task, 
                                                 task_to_thread, exec_state, 
                                                 thread_is_new, 
                                                 preemption_done, task_w, 
                                                 task_wa, pid_, head_, pid_s, 
                                                 head, pid_g, pid_t, pid_se, 
                                                 ctx_, pid_w, task_, pid_ta, 
                                                 thread, pid_m, thread_, pid_r, 
                                                 pid_th, ctx, pid_set, 
                                                 next_ctx_, pid_y, next_ctx, 
                                                 current_ctx_, pid_yi, task_y, 
                                                 next_thread, current_ctx, 
                                                 pid_ru, task_r, pid_f, task_f, 
                                                 pid_pr, pid, current_task, 
                                                 next_task, next_thread_, task >>

push_to_thread_pool(self) == wait_push_to_thread_pool(self)
                                \/ set_push_to_thread_pool(self)

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
                                                    lock_THREADS, 
                                                    lock_THREAD_POOL, 
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
                                                    thread_index, stored_ctx, 
                                                    stored_task, 
                                                    thread_to_task, 
                                                    task_to_thread, exec_state, 
                                                    thread_is_new, 
                                                    preemption_done, task_w, 
                                                    task_wa, pid_, head_, 
                                                    pid_s, head, pid_g, pid_t, 
                                                    pid_se, ctx_, pid_p, ctx_p, 
                                                    pid_ta, thread, pid_m, 
                                                    thread_, pid_r, pid_th, 
                                                    ctx, pid_set, next_ctx_, 
                                                    pid_y, next_ctx, 
                                                    current_ctx_, pid_yi, 
                                                    task_y, next_thread, 
                                                    current_ctx, pid_ru, 
                                                    task_r, pid_f, task_f, 
                                                    pid_pr, pid, current_task, 
                                                    next_task, next_thread_, 
                                                    task >>

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
                                                  lock_THREADS, 
                                                  lock_THREAD_POOL, 
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
                                                  stored_ctx, stored_task, 
                                                  thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  thread_is_new, 
                                                  preemption_done, task_wa, 
                                                  pid_, head_, pid_s, head, 
                                                  pid_g, pid_t, pid_se, ctx_, 
                                                  pid_p, ctx_p, pid_w, pid_ta, 
                                                  thread, pid_m, thread_, 
                                                  pid_r, pid_th, ctx, pid_set, 
                                                  next_ctx_, pid_y, next_ctx, 
                                                  current_ctx_, pid_yi, task_y, 
                                                  next_thread, current_ctx, 
                                                  pid_ru, task_r, pid_f, 
                                                  task_f, pid_pr, pid, 
                                                  current_task, next_task, 
                                                  next_thread_, task >>

end_wake_PREEMPTED_TASKS(self) == /\ pc[self] = "end_wake_PREEMPTED_TASKS"
                                  /\ pid_w' = [pid_w EXCEPT ![self] = pid_w[self]]
                                  /\ task_' = [task_ EXCEPT ![self] = defaultInitValue]
                                  /\ pc' = [pc EXCEPT ![self] = "check_wake_PREEMPTED_TASKS"]
                                  /\ UNCHANGED << queue, lock_info, 
                                                  lock_future, lock_scheduler, 
                                                  lock_THREADS, 
                                                  lock_THREAD_POOL, 
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
                                                  thread_index, stored_ctx, 
                                                  stored_task, thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  thread_is_new, 
                                                  preemption_done, stack, 
                                                  task_w, task_wa, pid_, head_, 
                                                  pid_s, head, pid_g, pid_t, 
                                                  pid_se, ctx_, pid_p, ctx_p, 
                                                  pid_ta, thread, pid_m, 
                                                  thread_, pid_r, pid_th, ctx, 
                                                  pid_set, next_ctx_, pid_y, 
                                                  next_ctx, current_ctx_, 
                                                  pid_yi, task_y, next_thread, 
                                                  current_ctx, pid_ru, task_r, 
                                                  pid_f, task_f, pid_pr, pid, 
                                                  current_task, next_task, 
                                                  next_thread_, task >>

wake_PREEMPTED_TASKS(self) == check_wake_PREEMPTED_TASKS(self)
                                 \/ pop_wake_PREEMPTED_TASKS(self)
                                 \/ end_wake_PREEMPTED_TASKS(self)

start_take_pooled_thread(self) == /\ pc[self] = "start_take_pooled_thread"
                                  /\ ~lock_THREADS
                                  /\ lock_THREADS' = TRUE
                                  /\ pc' = [pc EXCEPT ![self] = "end_take_pooled_thread"]
                                  /\ UNCHANGED << queue, lock_info, 
                                                  lock_future, lock_scheduler, 
                                                  lock_THREAD_POOL, 
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
                                                  thread_index, stored_ctx, 
                                                  stored_task, thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  thread_is_new, 
                                                  preemption_done, stack, 
                                                  task_w, task_wa, pid_, head_, 
                                                  pid_s, head, pid_g, pid_t, 
                                                  pid_se, ctx_, pid_p, ctx_p, 
                                                  pid_w, task_, pid_ta, thread, 
                                                  pid_m, thread_, pid_r, 
                                                  pid_th, ctx, pid_set, 
                                                  next_ctx_, pid_y, next_ctx, 
                                                  current_ctx_, pid_yi, task_y, 
                                                  next_thread, current_ctx, 
                                                  pid_ru, task_r, pid_f, 
                                                  task_f, pid_pr, pid, 
                                                  current_task, next_task, 
                                                  next_thread_, task >>

end_take_pooled_thread(self) == /\ pc[self] = "end_take_pooled_thread"
                                /\ IF THREADS_pooled = <<>>
                                      THEN /\ result_thread' = [result_thread EXCEPT ![pid_ta[self]] = -1]
                                           /\ UNCHANGED THREADS_pooled
                                      ELSE /\ result_thread' = [result_thread EXCEPT ![pid_ta[self]] = Head(THREADS_pooled)]
                                           /\ THREADS_pooled' = Tail(THREADS_pooled)
                                /\ lock_THREADS' = FALSE
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ pid_ta' = [pid_ta EXCEPT ![self] = Head(stack[self]).pid_ta]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << queue, lock_info, lock_future, 
                                                lock_scheduler, 
                                                lock_THREAD_POOL, 
                                                lock_PREEMPTED_TASKS, 
                                                lock_NEXT_TASK, 
                                                lock_result_context, in_queue, 
                                                need_sched, state, result_next, 
                                                result_future, result_context, 
                                                RUNNING, THREADS_running, 
                                                THREAD_POOL, PREEMPTED_TASKS, 
                                                NEXT_TASK, thread_index, 
                                                stored_ctx, stored_task, 
                                                thread_to_task, task_to_thread, 
                                                exec_state, thread_is_new, 
                                                preemption_done, task_w, 
                                                task_wa, pid_, head_, pid_s, 
                                                head, pid_g, pid_t, pid_se, 
                                                ctx_, pid_p, ctx_p, pid_w, 
                                                task_, thread, pid_m, thread_, 
                                                pid_r, pid_th, ctx, pid_set, 
                                                next_ctx_, pid_y, next_ctx, 
                                                current_ctx_, pid_yi, task_y, 
                                                next_thread, current_ctx, 
                                                pid_ru, task_r, pid_f, task_f, 
                                                pid_pr, pid, current_task, 
                                                next_task, next_thread_, task >>

take_pooled_thread(self) == start_take_pooled_thread(self)
                               \/ end_take_pooled_thread(self)

wait_make_thread_pooled(self) == /\ pc[self] = "wait_make_thread_pooled"
                                 /\ ~lock_THREADS
                                 /\ lock_THREADS' = TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "push_make_thread_pooled"]
                                 /\ UNCHANGED << queue, lock_info, lock_future, 
                                                 lock_scheduler, 
                                                 lock_THREAD_POOL, 
                                                 lock_PREEMPTED_TASKS, 
                                                 lock_NEXT_TASK, 
                                                 lock_result_context, in_queue, 
                                                 need_sched, state, 
                                                 result_next, result_future, 
                                                 result_context, result_thread, 
                                                 RUNNING, THREADS_pooled, 
                                                 THREADS_running, THREAD_POOL, 
                                                 PREEMPTED_TASKS, NEXT_TASK, 
                                                 thread_index, stored_ctx, 
                                                 stored_task, thread_to_task, 
                                                 task_to_thread, exec_state, 
                                                 thread_is_new, 
                                                 preemption_done, stack, 
                                                 task_w, task_wa, pid_, head_, 
                                                 pid_s, head, pid_g, pid_t, 
                                                 pid_se, ctx_, pid_p, ctx_p, 
                                                 pid_w, task_, pid_ta, thread, 
                                                 pid_m, thread_, pid_r, pid_th, 
                                                 ctx, pid_set, next_ctx_, 
                                                 pid_y, next_ctx, current_ctx_, 
                                                 pid_yi, task_y, next_thread, 
                                                 current_ctx, pid_ru, task_r, 
                                                 pid_f, task_f, pid_pr, pid, 
                                                 current_task, next_task, 
                                                 next_thread_, task >>

push_make_thread_pooled(self) == /\ pc[self] = "push_make_thread_pooled"
                                 /\ THREADS_pooled' = Append(THREADS_pooled, thread[self])
                                 /\ lock_THREADS' = FALSE
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ thread' = [thread EXCEPT ![self] = Head(stack[self]).thread]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                 /\ UNCHANGED << queue, lock_info, lock_future, 
                                                 lock_scheduler, 
                                                 lock_THREAD_POOL, 
                                                 lock_PREEMPTED_TASKS, 
                                                 lock_NEXT_TASK, 
                                                 lock_result_context, in_queue, 
                                                 need_sched, state, 
                                                 result_next, result_future, 
                                                 result_context, result_thread, 
                                                 RUNNING, THREADS_running, 
                                                 THREAD_POOL, PREEMPTED_TASKS, 
                                                 NEXT_TASK, thread_index, 
                                                 stored_ctx, stored_task, 
                                                 thread_to_task, 
                                                 task_to_thread, exec_state, 
                                                 thread_is_new, 
                                                 preemption_done, task_w, 
                                                 task_wa, pid_, head_, pid_s, 
                                                 head, pid_g, pid_t, pid_se, 
                                                 ctx_, pid_p, ctx_p, pid_w, 
                                                 task_, pid_ta, pid_m, thread_, 
                                                 pid_r, pid_th, ctx, pid_set, 
                                                 next_ctx_, pid_y, next_ctx, 
                                                 current_ctx_, pid_yi, task_y, 
                                                 next_thread, current_ctx, 
                                                 pid_ru, task_r, pid_f, task_f, 
                                                 pid_pr, pid, current_task, 
                                                 next_task, next_thread_, task >>

make_thread_pooled(self) == wait_make_thread_pooled(self)
                               \/ push_make_thread_pooled(self)

check_make_all_threads_pooled(self) == /\ pc[self] = "check_make_all_threads_pooled"
                                       /\ IF THREAD_POOL[pid_m[self]] = <<>>
                                             THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                  /\ thread_' = [thread_ EXCEPT ![self] = Head(stack[self]).thread_]
                                                  /\ pid_m' = [pid_m EXCEPT ![self] = Head(stack[self]).pid_m]
                                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                             ELSE /\ pc' = [pc EXCEPT ![self] = "pop_make_all_threads_pooled"]
                                                  /\ UNCHANGED << stack, pid_m, 
                                                                  thread_ >>
                                       /\ UNCHANGED << queue, lock_info, 
                                                       lock_future, 
                                                       lock_scheduler, 
                                                       lock_THREADS, 
                                                       lock_THREAD_POOL, 
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
                                                       stored_ctx, stored_task, 
                                                       thread_to_task, 
                                                       task_to_thread, 
                                                       exec_state, 
                                                       thread_is_new, 
                                                       preemption_done, task_w, 
                                                       task_wa, pid_, head_, 
                                                       pid_s, head, pid_g, 
                                                       pid_t, pid_se, ctx_, 
                                                       pid_p, ctx_p, pid_w, 
                                                       task_, pid_ta, thread, 
                                                       pid_r, pid_th, ctx, 
                                                       pid_set, next_ctx_, 
                                                       pid_y, next_ctx, 
                                                       current_ctx_, pid_yi, 
                                                       task_y, next_thread, 
                                                       current_ctx, pid_ru, 
                                                       task_r, pid_f, task_f, 
                                                       pid_pr, pid, 
                                                       current_task, next_task, 
                                                       next_thread_, task >>

pop_make_all_threads_pooled(self) == /\ pc[self] = "pop_make_all_threads_pooled"
                                     /\ thread_' = [thread_ EXCEPT ![self] = Head(THREAD_POOL[pid_m[self]])]
                                     /\ THREAD_POOL' = [THREAD_POOL EXCEPT ![pid_m[self]] = Tail(THREAD_POOL[pid_m[self]])]
                                     /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "make_thread_pooled",
                                                                                 pc        |->  "end_make_all_threads_pooled",
                                                                                 thread    |->  thread[self] ] >>
                                                                             \o stack[self]]
                                        /\ thread' = [thread EXCEPT ![self] = thread_'[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "wait_make_thread_pooled"]
                                     /\ UNCHANGED << queue, lock_info, 
                                                     lock_future, 
                                                     lock_scheduler, 
                                                     lock_THREADS, 
                                                     lock_THREAD_POOL, 
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
                                                     PREEMPTED_TASKS, 
                                                     NEXT_TASK, thread_index, 
                                                     stored_ctx, stored_task, 
                                                     thread_to_task, 
                                                     task_to_thread, 
                                                     exec_state, thread_is_new, 
                                                     preemption_done, task_w, 
                                                     task_wa, pid_, head_, 
                                                     pid_s, head, pid_g, pid_t, 
                                                     pid_se, ctx_, pid_p, 
                                                     ctx_p, pid_w, task_, 
                                                     pid_ta, pid_m, pid_r, 
                                                     pid_th, ctx, pid_set, 
                                                     next_ctx_, pid_y, 
                                                     next_ctx, current_ctx_, 
                                                     pid_yi, task_y, 
                                                     next_thread, current_ctx, 
                                                     pid_ru, task_r, pid_f, 
                                                     task_f, pid_pr, pid, 
                                                     current_task, next_task, 
                                                     next_thread_, task >>

end_make_all_threads_pooled(self) == /\ pc[self] = "end_make_all_threads_pooled"
                                     /\ pid_m' = [pid_m EXCEPT ![self] = pid_m[self]]
                                     /\ thread_' = [thread_ EXCEPT ![self] = defaultInitValue]
                                     /\ pc' = [pc EXCEPT ![self] = "check_make_all_threads_pooled"]
                                     /\ UNCHANGED << queue, lock_info, 
                                                     lock_future, 
                                                     lock_scheduler, 
                                                     lock_THREADS, 
                                                     lock_THREAD_POOL, 
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
                                                     stored_ctx, stored_task, 
                                                     thread_to_task, 
                                                     task_to_thread, 
                                                     exec_state, thread_is_new, 
                                                     preemption_done, stack, 
                                                     task_w, task_wa, pid_, 
                                                     head_, pid_s, head, pid_g, 
                                                     pid_t, pid_se, ctx_, 
                                                     pid_p, ctx_p, pid_w, 
                                                     task_, pid_ta, thread, 
                                                     pid_r, pid_th, ctx, 
                                                     pid_set, next_ctx_, pid_y, 
                                                     next_ctx, current_ctx_, 
                                                     pid_yi, task_y, 
                                                     next_thread, current_ctx, 
                                                     pid_ru, task_r, pid_f, 
                                                     task_f, pid_pr, pid, 
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
                                                    lock_THREADS, 
                                                    lock_THREAD_POOL, 
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
                                                    thread_index, stored_ctx, 
                                                    stored_task, 
                                                    thread_to_task, 
                                                    task_to_thread, exec_state, 
                                                    thread_is_new, 
                                                    preemption_done, stack, 
                                                    task_w, task_wa, pid_, 
                                                    head_, pid_s, head, pid_g, 
                                                    pid_t, pid_se, ctx_, pid_p, 
                                                    ctx_p, pid_w, task_, 
                                                    pid_ta, thread, pid_m, 
                                                    thread_, pid_r, pid_th, 
                                                    ctx, pid_set, next_ctx_, 
                                                    pid_y, next_ctx, 
                                                    current_ctx_, pid_yi, 
                                                    task_y, next_thread, 
                                                    current_ctx, pid_ru, 
                                                    task_r, pid_f, task_f, 
                                                    pid_pr, pid, current_task, 
                                                    next_task, next_thread_, 
                                                    task >>

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
                                          lock_scheduler, lock_THREADS, 
                                          lock_THREAD_POOL, 
                                          lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                          lock_result_context, in_queue, 
                                          need_sched, state, result_next, 
                                          result_future, result_context, 
                                          result_thread, RUNNING, 
                                          THREADS_pooled, THREADS_running, 
                                          THREAD_POOL, PREEMPTED_TASKS, 
                                          NEXT_TASK, thread_index, stored_ctx, 
                                          stored_task, thread_to_task, 
                                          task_to_thread, exec_state, 
                                          thread_is_new, preemption_done, 
                                          task_w, task_wa, pid_, head_, pid_s, 
                                          head, pid_g, pid_t, pid_se, ctx_, 
                                          pid_p, ctx_p, pid_ta, thread, pid_m, 
                                          thread_, pid_r, pid_th, ctx, pid_set, 
                                          next_ctx_, pid_y, next_ctx, 
                                          current_ctx_, pid_yi, task_y, 
                                          next_thread, current_ctx, pid_ru, 
                                          task_r, pid_f, task_f, pid_pr, pid, 
                                          current_task, next_task, 
                                          next_thread_, task >>

unlock_preempted_re_schedule(self) == /\ pc[self] = "unlock_preempted_re_schedule"
                                      /\ lock_PREEMPTED_TASKS' = [lock_PREEMPTED_TASKS EXCEPT ![pid_r[self]] = FALSE]
                                      /\ pc' = [pc EXCEPT ![self] = "lock_pool_re_schedule"]
                                      /\ UNCHANGED << queue, lock_info, 
                                                      lock_future, 
                                                      lock_scheduler, 
                                                      lock_THREADS, 
                                                      lock_THREAD_POOL, 
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
                                                      stored_ctx, stored_task, 
                                                      thread_to_task, 
                                                      task_to_thread, 
                                                      exec_state, 
                                                      thread_is_new, 
                                                      preemption_done, stack, 
                                                      task_w, task_wa, pid_, 
                                                      head_, pid_s, head, 
                                                      pid_g, pid_t, pid_se, 
                                                      ctx_, pid_p, ctx_p, 
                                                      pid_w, task_, pid_ta, 
                                                      thread, pid_m, thread_, 
                                                      pid_r, pid_th, ctx, 
                                                      pid_set, next_ctx_, 
                                                      pid_y, next_ctx, 
                                                      current_ctx_, pid_yi, 
                                                      task_y, next_thread, 
                                                      current_ctx, pid_ru, 
                                                      task_r, pid_f, task_f, 
                                                      pid_pr, pid, 
                                                      current_task, next_task, 
                                                      next_thread_, task >>

lock_pool_re_schedule(self) == /\ pc[self] = "lock_pool_re_schedule"
                               /\ ~lock_THREAD_POOL[pid_r[self]]
                               /\ lock_THREAD_POOL' = [lock_THREAD_POOL EXCEPT ![pid_r[self]] = TRUE]
                               /\ pc' = [pc EXCEPT ![self] = "pool_re_schedule"]
                               /\ UNCHANGED << queue, lock_info, lock_future, 
                                               lock_scheduler, lock_THREADS, 
                                               lock_PREEMPTED_TASKS, 
                                               lock_NEXT_TASK, 
                                               lock_result_context, in_queue, 
                                               need_sched, state, result_next, 
                                               result_future, result_context, 
                                               result_thread, RUNNING, 
                                               THREADS_pooled, THREADS_running, 
                                               THREAD_POOL, PREEMPTED_TASKS, 
                                               NEXT_TASK, thread_index, 
                                               stored_ctx, stored_task, 
                                               thread_to_task, task_to_thread, 
                                               exec_state, thread_is_new, 
                                               preemption_done, stack, task_w, 
                                               task_wa, pid_, head_, pid_s, 
                                               head, pid_g, pid_t, pid_se, 
                                               ctx_, pid_p, ctx_p, pid_w, 
                                               task_, pid_ta, thread, pid_m, 
                                               thread_, pid_r, pid_th, ctx, 
                                               pid_set, next_ctx_, pid_y, 
                                               next_ctx, current_ctx_, pid_yi, 
                                               task_y, next_thread, 
                                               current_ctx, pid_ru, task_r, 
                                               pid_f, task_f, pid_pr, pid, 
                                               current_task, next_task, 
                                               next_thread_, task >>

pool_re_schedule(self) == /\ pc[self] = "pool_re_schedule"
                          /\ /\ pid_m' = [pid_m EXCEPT ![self] = pid_r[self]]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "make_all_threads_pooled",
                                                                      pc        |->  "unlock_pool_re_schedule",
                                                                      thread_   |->  thread_[self],
                                                                      pid_m     |->  pid_m[self] ] >>
                                                                  \o stack[self]]
                          /\ thread_' = [thread_ EXCEPT ![self] = defaultInitValue]
                          /\ pc' = [pc EXCEPT ![self] = "check_make_all_threads_pooled"]
                          /\ UNCHANGED << queue, lock_info, lock_future, 
                                          lock_scheduler, lock_THREADS, 
                                          lock_THREAD_POOL, 
                                          lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                          lock_result_context, in_queue, 
                                          need_sched, state, result_next, 
                                          result_future, result_context, 
                                          result_thread, RUNNING, 
                                          THREADS_pooled, THREADS_running, 
                                          THREAD_POOL, PREEMPTED_TASKS, 
                                          NEXT_TASK, thread_index, stored_ctx, 
                                          stored_task, thread_to_task, 
                                          task_to_thread, exec_state, 
                                          thread_is_new, preemption_done, 
                                          task_w, task_wa, pid_, head_, pid_s, 
                                          head, pid_g, pid_t, pid_se, ctx_, 
                                          pid_p, ctx_p, pid_w, task_, pid_ta, 
                                          thread, pid_r, pid_th, ctx, pid_set, 
                                          next_ctx_, pid_y, next_ctx, 
                                          current_ctx_, pid_yi, task_y, 
                                          next_thread, current_ctx, pid_ru, 
                                          task_r, pid_f, task_f, pid_pr, pid, 
                                          current_task, next_task, 
                                          next_thread_, task >>

unlock_pool_re_schedule(self) == /\ pc[self] = "unlock_pool_re_schedule"
                                 /\ lock_THREAD_POOL' = [lock_THREAD_POOL EXCEPT ![pid_r[self]] = FALSE]
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ pid_r' = [pid_r EXCEPT ![self] = Head(stack[self]).pid_r]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                 /\ UNCHANGED << queue, lock_info, lock_future, 
                                                 lock_scheduler, lock_THREADS, 
                                                 lock_PREEMPTED_TASKS, 
                                                 lock_NEXT_TASK, 
                                                 lock_result_context, in_queue, 
                                                 need_sched, state, 
                                                 result_next, result_future, 
                                                 result_context, result_thread, 
                                                 RUNNING, THREADS_pooled, 
                                                 THREADS_running, THREAD_POOL, 
                                                 PREEMPTED_TASKS, NEXT_TASK, 
                                                 thread_index, stored_ctx, 
                                                 stored_task, thread_to_task, 
                                                 task_to_thread, exec_state, 
                                                 thread_is_new, 
                                                 preemption_done, task_w, 
                                                 task_wa, pid_, head_, pid_s, 
                                                 head, pid_g, pid_t, pid_se, 
                                                 ctx_, pid_p, ctx_p, pid_w, 
                                                 task_, pid_ta, thread, pid_m, 
                                                 thread_, pid_th, ctx, pid_set, 
                                                 next_ctx_, pid_y, next_ctx, 
                                                 current_ctx_, pid_yi, task_y, 
                                                 next_thread, current_ctx, 
                                                 pid_ru, task_r, pid_f, task_f, 
                                                 pid_pr, pid, current_task, 
                                                 next_task, next_thread_, task >>

re_schedule(self) == lock_preempted_re_schedule(self)
                        \/ wake_re_schedule(self)
                        \/ unlock_preempted_re_schedule(self)
                        \/ lock_pool_re_schedule(self)
                        \/ pool_re_schedule(self)
                        \/ unlock_pool_re_schedule(self)

start_thread_entry(self) == /\ pc[self] = "start_thread_entry"
                            /\ /\ ctx_' = [ctx_ EXCEPT ![self] = ctx[self]]
                               /\ pid_se' = [pid_se EXCEPT ![self] = pid_th[self]]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_current_context",
                                                                        pc        |->  "re_schedule_thread_entry",
                                                                        pid_se    |->  pid_se[self],
                                                                        ctx_      |->  ctx_[self] ] >>
                                                                    \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "wait_set_current_context"]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, lock_THREADS, 
                                            lock_THREAD_POOL, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, state, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREADS_running, 
                                            THREAD_POOL, PREEMPTED_TASKS, 
                                            NEXT_TASK, thread_index, 
                                            stored_ctx, stored_task, 
                                            thread_to_task, task_to_thread, 
                                            exec_state, thread_is_new, 
                                            preemption_done, task_w, task_wa, 
                                            pid_, head_, pid_s, head, pid_g, 
                                            pid_t, pid_p, ctx_p, pid_w, task_, 
                                            pid_ta, thread, pid_m, thread_, 
                                            pid_r, pid_th, ctx, pid_set, 
                                            next_ctx_, pid_y, next_ctx, 
                                            current_ctx_, pid_yi, task_y, 
                                            next_thread, current_ctx, pid_ru, 
                                            task_r, pid_f, task_f, pid_pr, pid, 
                                            current_task, next_task, 
                                            next_thread_, task >>

re_schedule_thread_entry(self) == /\ pc[self] = "re_schedule_thread_entry"
                                  /\ /\ pid_r' = [pid_r EXCEPT ![self] = pid_th[self]]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "re_schedule",
                                                                              pc        |->  "end_thread_entry",
                                                                              pid_r     |->  pid_r[self] ] >>
                                                                          \o stack[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "lock_preempted_re_schedule"]
                                  /\ UNCHANGED << queue, lock_info, 
                                                  lock_future, lock_scheduler, 
                                                  lock_THREADS, 
                                                  lock_THREAD_POOL, 
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
                                                  thread_index, stored_ctx, 
                                                  stored_task, thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  thread_is_new, 
                                                  preemption_done, task_w, 
                                                  task_wa, pid_, head_, pid_s, 
                                                  head, pid_g, pid_t, pid_se, 
                                                  ctx_, pid_p, ctx_p, pid_w, 
                                                  task_, pid_ta, thread, pid_m, 
                                                  thread_, pid_th, ctx, 
                                                  pid_set, next_ctx_, pid_y, 
                                                  next_ctx, current_ctx_, 
                                                  pid_yi, task_y, next_thread, 
                                                  current_ctx, pid_ru, task_r, 
                                                  pid_f, task_f, pid_pr, pid, 
                                                  current_task, next_task, 
                                                  next_thread_, task >>

end_thread_entry(self) == /\ pc[self] = "end_thread_entry"
                          /\ /\ pid_ru' = [pid_ru EXCEPT ![self] = pid_th[self]]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "run_main",
                                                                      pc        |->  "Error",
                                                                      task_r    |->  task_r[self],
                                                                      pid_ru    |->  pid_ru[self] ] >>
                                                                  \o stack[self]]
                          /\ task_r' = [task_r EXCEPT ![self] = defaultInitValue]
                          /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                          /\ UNCHANGED << queue, lock_info, lock_future, 
                                          lock_scheduler, lock_THREADS, 
                                          lock_THREAD_POOL, 
                                          lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                          lock_result_context, in_queue, 
                                          need_sched, state, result_next, 
                                          result_future, result_context, 
                                          result_thread, RUNNING, 
                                          THREADS_pooled, THREADS_running, 
                                          THREAD_POOL, PREEMPTED_TASKS, 
                                          NEXT_TASK, thread_index, stored_ctx, 
                                          stored_task, thread_to_task, 
                                          task_to_thread, exec_state, 
                                          thread_is_new, preemption_done, 
                                          task_w, task_wa, pid_, head_, pid_s, 
                                          head, pid_g, pid_t, pid_se, ctx_, 
                                          pid_p, ctx_p, pid_w, task_, pid_ta, 
                                          thread, pid_m, thread_, pid_r, 
                                          pid_th, ctx, pid_set, next_ctx_, 
                                          pid_y, next_ctx, current_ctx_, 
                                          pid_yi, task_y, next_thread, 
                                          current_ctx, pid_f, task_f, pid_pr, 
                                          pid, current_task, next_task, 
                                          next_thread_, task >>

thread_entry(self) == start_thread_entry(self)
                         \/ re_schedule_thread_entry(self)
                         \/ end_thread_entry(self)

start_set_exec_state(self) == /\ pc[self] = "start_set_exec_state"
                              /\ THREADS_running' = [THREADS_running EXCEPT ![pid_set[self]] = next_ctx_[self]]
                              /\ next_task' = [next_task EXCEPT ![self] = thread_to_task[next_ctx_[self]]]
                              /\ IF next_task'[self] > 0
                                    THEN /\ RUNNING' = [RUNNING EXCEPT ![pid_set[self]] = next_task'[self]]
                                         /\ exec_state' = [exec_state EXCEPT ![pid_set[self]] = "Preempted"]
                                         /\ pc' = [pc EXCEPT ![self] = "end_set_exec_state"]
                                         /\ UNCHANGED << thread_is_new, stack, 
                                                         pid_th, ctx >>
                                    ELSE /\ IF thread_is_new[next_ctx_[self]] = TRUE
                                               THEN /\ thread_is_new' = [thread_is_new EXCEPT ![next_ctx_[self]] = FALSE]
                                                    /\ /\ ctx' = [ctx EXCEPT ![self] = next_ctx_[self]]
                                                       /\ pid_th' = [pid_th EXCEPT ![self] = pid_set[self]]
                                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "thread_entry",
                                                                                                pc        |->  "end_set_exec_state",
                                                                                                pid_th    |->  pid_th[self],
                                                                                                ctx       |->  ctx[self] ] >>
                                                                                            \o stack[self]]
                                                    /\ pc' = [pc EXCEPT ![self] = "start_thread_entry"]
                                                    /\ UNCHANGED exec_state
                                               ELSE /\ exec_state' = [exec_state EXCEPT ![pid_set[self]] = "Yielded"]
                                                    /\ pc' = [pc EXCEPT ![self] = "end_set_exec_state"]
                                                    /\ UNCHANGED << thread_is_new, 
                                                                    stack, 
                                                                    pid_th, 
                                                                    ctx >>
                                         /\ UNCHANGED RUNNING
                              /\ UNCHANGED << queue, lock_info, lock_future, 
                                              lock_scheduler, lock_THREADS, 
                                              lock_THREAD_POOL, 
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
                                              preemption_done, task_w, task_wa, 
                                              pid_, head_, pid_s, head, pid_g, 
                                              pid_t, pid_se, ctx_, pid_p, 
                                              ctx_p, pid_w, task_, pid_ta, 
                                              thread, pid_m, thread_, pid_r, 
                                              pid_set, next_ctx_, pid_y, 
                                              next_ctx, current_ctx_, pid_yi, 
                                              task_y, next_thread, current_ctx, 
                                              pid_ru, task_r, pid_f, task_f, 
                                              pid_pr, pid, current_task, 
                                              next_thread_, task >>

end_set_exec_state(self) == /\ pc[self] = "end_set_exec_state"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ pid_set' = [pid_set EXCEPT ![self] = Head(stack[self]).pid_set]
                            /\ next_ctx_' = [next_ctx_ EXCEPT ![self] = Head(stack[self]).next_ctx_]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, lock_THREADS, 
                                            lock_THREAD_POOL, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, state, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREADS_running, 
                                            THREAD_POOL, PREEMPTED_TASKS, 
                                            NEXT_TASK, thread_index, 
                                            stored_ctx, stored_task, 
                                            thread_to_task, task_to_thread, 
                                            exec_state, thread_is_new, 
                                            preemption_done, task_w, task_wa, 
                                            pid_, head_, pid_s, head, pid_g, 
                                            pid_t, pid_se, ctx_, pid_p, ctx_p, 
                                            pid_w, task_, pid_ta, thread, 
                                            pid_m, thread_, pid_r, pid_th, ctx, 
                                            pid_y, next_ctx, current_ctx_, 
                                            pid_yi, task_y, next_thread, 
                                            current_ctx, pid_ru, task_r, pid_f, 
                                            task_f, pid_pr, pid, current_task, 
                                            next_task, next_thread_, task >>

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
                                                    /\ pc' = [pc EXCEPT ![self] = "set_ctx_yield_and_pool"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "lock_result_yield_and_pool"]
                                                    /\ UNCHANGED << exec_state, 
                                                                    current_ctx_ >>
                              /\ UNCHANGED << queue, lock_info, lock_future, 
                                              lock_scheduler, lock_THREADS, 
                                              lock_THREAD_POOL, 
                                              lock_PREEMPTED_TASKS, 
                                              lock_NEXT_TASK, 
                                              lock_result_context, in_queue, 
                                              need_sched, state, result_next, 
                                              result_future, result_context, 
                                              result_thread, RUNNING, 
                                              THREADS_pooled, THREADS_running, 
                                              THREAD_POOL, PREEMPTED_TASKS, 
                                              NEXT_TASK, thread_index, 
                                              stored_ctx, stored_task, 
                                              thread_to_task, task_to_thread, 
                                              thread_is_new, preemption_done, 
                                              stack, task_w, task_wa, pid_, 
                                              head_, pid_s, head, pid_g, pid_t, 
                                              pid_se, ctx_, pid_p, ctx_p, 
                                              pid_w, task_, pid_ta, thread, 
                                              pid_m, thread_, pid_r, pid_th, 
                                              ctx, pid_set, next_ctx_, pid_y, 
                                              next_ctx, pid_yi, task_y, 
                                              next_thread, current_ctx, pid_ru, 
                                              task_r, pid_f, task_f, pid_pr, 
                                              pid, current_task, next_task, 
                                              next_thread_, task >>

lock_result_yield_and_pool(self) == /\ pc[self] = "lock_result_yield_and_pool"
                                    /\ ~lock_result_context
                                    /\ lock_result_context' = TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "get_ctx_yield_and_pool"]
                                    /\ UNCHANGED << queue, lock_info, 
                                                    lock_future, 
                                                    lock_scheduler, 
                                                    lock_THREADS, 
                                                    lock_THREAD_POOL, 
                                                    lock_PREEMPTED_TASKS, 
                                                    lock_NEXT_TASK, in_queue, 
                                                    need_sched, state, 
                                                    result_next, result_future, 
                                                    result_context, 
                                                    result_thread, RUNNING, 
                                                    THREADS_pooled, 
                                                    THREADS_running, 
                                                    THREAD_POOL, 
                                                    PREEMPTED_TASKS, NEXT_TASK, 
                                                    thread_index, stored_ctx, 
                                                    stored_task, 
                                                    thread_to_task, 
                                                    task_to_thread, exec_state, 
                                                    thread_is_new, 
                                                    preemption_done, stack, 
                                                    task_w, task_wa, pid_, 
                                                    head_, pid_s, head, pid_g, 
                                                    pid_t, pid_se, ctx_, pid_p, 
                                                    ctx_p, pid_w, task_, 
                                                    pid_ta, thread, pid_m, 
                                                    thread_, pid_r, pid_th, 
                                                    ctx, pid_set, next_ctx_, 
                                                    pid_y, next_ctx, 
                                                    current_ctx_, pid_yi, 
                                                    task_y, next_thread, 
                                                    current_ctx, pid_ru, 
                                                    task_r, pid_f, task_f, 
                                                    pid_pr, pid, current_task, 
                                                    next_task, next_thread_, 
                                                    task >>

get_ctx_yield_and_pool(self) == /\ pc[self] = "get_ctx_yield_and_pool"
                                /\ /\ pid_t' = [pid_t EXCEPT ![self] = pid_y[self]]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "take_current_context",
                                                                            pc        |->  "unlock_result_yield_and_pool",
                                                                            pid_t     |->  pid_t[self] ] >>
                                                                        \o stack[self]]
                                /\ pc' = [pc EXCEPT ![self] = "wait_take_current_context"]
                                /\ UNCHANGED << queue, lock_info, lock_future, 
                                                lock_scheduler, lock_THREADS, 
                                                lock_THREAD_POOL, 
                                                lock_PREEMPTED_TASKS, 
                                                lock_NEXT_TASK, 
                                                lock_result_context, in_queue, 
                                                need_sched, state, result_next, 
                                                result_future, result_context, 
                                                result_thread, RUNNING, 
                                                THREADS_pooled, 
                                                THREADS_running, THREAD_POOL, 
                                                PREEMPTED_TASKS, NEXT_TASK, 
                                                thread_index, stored_ctx, 
                                                stored_task, thread_to_task, 
                                                task_to_thread, exec_state, 
                                                thread_is_new, preemption_done, 
                                                task_w, task_wa, pid_, head_, 
                                                pid_s, head, pid_g, pid_se, 
                                                ctx_, pid_p, ctx_p, pid_w, 
                                                task_, pid_ta, thread, pid_m, 
                                                thread_, pid_r, pid_th, ctx, 
                                                pid_set, next_ctx_, pid_y, 
                                                next_ctx, current_ctx_, pid_yi, 
                                                task_y, next_thread, 
                                                current_ctx, pid_ru, task_r, 
                                                pid_f, task_f, pid_pr, pid, 
                                                current_task, next_task, 
                                                next_thread_, task >>

unlock_result_yield_and_pool(self) == /\ pc[self] = "unlock_result_yield_and_pool"
                                      /\ current_ctx_' = [current_ctx_ EXCEPT ![self] = result_context]
                                      /\ lock_result_context' = FALSE
                                      /\ pc' = [pc EXCEPT ![self] = "push_ctx_yield_and_pool"]
                                      /\ UNCHANGED << queue, lock_info, 
                                                      lock_future, 
                                                      lock_scheduler, 
                                                      lock_THREADS, 
                                                      lock_THREAD_POOL, 
                                                      lock_PREEMPTED_TASKS, 
                                                      lock_NEXT_TASK, in_queue, 
                                                      need_sched, state, 
                                                      result_next, 
                                                      result_future, 
                                                      result_context, 
                                                      result_thread, RUNNING, 
                                                      THREADS_pooled, 
                                                      THREADS_running, 
                                                      THREAD_POOL, 
                                                      PREEMPTED_TASKS, 
                                                      NEXT_TASK, thread_index, 
                                                      stored_ctx, stored_task, 
                                                      thread_to_task, 
                                                      task_to_thread, 
                                                      exec_state, 
                                                      thread_is_new, 
                                                      preemption_done, stack, 
                                                      task_w, task_wa, pid_, 
                                                      head_, pid_s, head, 
                                                      pid_g, pid_t, pid_se, 
                                                      ctx_, pid_p, ctx_p, 
                                                      pid_w, task_, pid_ta, 
                                                      thread, pid_m, thread_, 
                                                      pid_r, pid_th, ctx, 
                                                      pid_set, next_ctx_, 
                                                      pid_y, next_ctx, pid_yi, 
                                                      task_y, next_thread, 
                                                      current_ctx, pid_ru, 
                                                      task_r, pid_f, task_f, 
                                                      pid_pr, pid, 
                                                      current_task, next_task, 
                                                      next_thread_, task >>

push_ctx_yield_and_pool(self) == /\ pc[self] = "push_ctx_yield_and_pool"
                                 /\ /\ ctx_p' = [ctx_p EXCEPT ![self] = current_ctx_[self]]
                                    /\ pid_p' = [pid_p EXCEPT ![self] = pid_y[self]]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "push_to_thread_pool",
                                                                             pc        |->  "context_switch_yield_and_pool",
                                                                             pid_p     |->  pid_p[self],
                                                                             ctx_p     |->  ctx_p[self] ] >>
                                                                         \o stack[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "wait_push_to_thread_pool"]
                                 /\ UNCHANGED << queue, lock_info, lock_future, 
                                                 lock_scheduler, lock_THREADS, 
                                                 lock_THREAD_POOL, 
                                                 lock_PREEMPTED_TASKS, 
                                                 lock_NEXT_TASK, 
                                                 lock_result_context, in_queue, 
                                                 need_sched, state, 
                                                 result_next, result_future, 
                                                 result_context, result_thread, 
                                                 RUNNING, THREADS_pooled, 
                                                 THREADS_running, THREAD_POOL, 
                                                 PREEMPTED_TASKS, NEXT_TASK, 
                                                 thread_index, stored_ctx, 
                                                 stored_task, thread_to_task, 
                                                 task_to_thread, exec_state, 
                                                 thread_is_new, 
                                                 preemption_done, task_w, 
                                                 task_wa, pid_, head_, pid_s, 
                                                 head, pid_g, pid_t, pid_se, 
                                                 ctx_, pid_w, task_, pid_ta, 
                                                 thread, pid_m, thread_, pid_r, 
                                                 pid_th, ctx, pid_set, 
                                                 next_ctx_, pid_y, next_ctx, 
                                                 current_ctx_, pid_yi, task_y, 
                                                 next_thread, current_ctx, 
                                                 pid_ru, task_r, pid_f, task_f, 
                                                 pid_pr, pid, current_task, 
                                                 next_task, next_thread_, task >>

context_switch_yield_and_pool(self) == /\ pc[self] = "context_switch_yield_and_pool"
                                       /\ stored_task' = [stored_task EXCEPT ![pid_y[self]] = thread_to_task[next_ctx[self]]]
                                       /\ stored_ctx' = [stored_ctx EXCEPT ![pid_y[self]] = next_ctx[self]]
                                       /\ /\ current_ctx_' = [current_ctx_ EXCEPT ![self] = Head(stack[self]).current_ctx_]
                                          /\ next_ctx_' = [next_ctx_ EXCEPT ![self] = next_ctx[self]]
                                          /\ pid_set' = [pid_set EXCEPT ![self] = pid_y[self]]
                                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_exec_state",
                                                                                   pc        |->  Head(stack[self]).pc,
                                                                                   pid_set   |->  pid_set[self],
                                                                                   next_ctx_ |->  next_ctx_[self] ] >>
                                                                               \o Tail(stack[self])]
                                       /\ pc' = [pc EXCEPT ![self] = "start_set_exec_state"]
                                       /\ UNCHANGED << queue, lock_info, 
                                                       lock_future, 
                                                       lock_scheduler, 
                                                       lock_THREADS, 
                                                       lock_THREAD_POOL, 
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
                                                       thread_to_task, 
                                                       task_to_thread, 
                                                       exec_state, 
                                                       thread_is_new, 
                                                       preemption_done, task_w, 
                                                       task_wa, pid_, head_, 
                                                       pid_s, head, pid_g, 
                                                       pid_t, pid_se, ctx_, 
                                                       pid_p, ctx_p, pid_w, 
                                                       task_, pid_ta, thread, 
                                                       pid_m, thread_, pid_r, 
                                                       pid_th, ctx, pid_y, 
                                                       next_ctx, pid_yi, 
                                                       task_y, next_thread, 
                                                       current_ctx, pid_ru, 
                                                       task_r, pid_f, task_f, 
                                                       pid_pr, pid, 
                                                       current_task, next_task, 
                                                       next_thread_, task >>

set_ctx_yield_and_pool(self) == /\ pc[self] = "set_ctx_yield_and_pool"
                                /\ /\ ctx_' = [ctx_ EXCEPT ![self] = current_ctx_[self]]
                                   /\ pid_se' = [pid_se EXCEPT ![self] = pid_y[self]]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_current_context",
                                                                            pc        |->  "re_schedule_yield_and_pool",
                                                                            pid_se    |->  pid_se[self],
                                                                            ctx_      |->  ctx_[self] ] >>
                                                                        \o stack[self]]
                                /\ pc' = [pc EXCEPT ![self] = "wait_set_current_context"]
                                /\ UNCHANGED << queue, lock_info, lock_future, 
                                                lock_scheduler, lock_THREADS, 
                                                lock_THREAD_POOL, 
                                                lock_PREEMPTED_TASKS, 
                                                lock_NEXT_TASK, 
                                                lock_result_context, in_queue, 
                                                need_sched, state, result_next, 
                                                result_future, result_context, 
                                                result_thread, RUNNING, 
                                                THREADS_pooled, 
                                                THREADS_running, THREAD_POOL, 
                                                PREEMPTED_TASKS, NEXT_TASK, 
                                                thread_index, stored_ctx, 
                                                stored_task, thread_to_task, 
                                                task_to_thread, exec_state, 
                                                thread_is_new, preemption_done, 
                                                task_w, task_wa, pid_, head_, 
                                                pid_s, head, pid_g, pid_t, 
                                                pid_p, ctx_p, pid_w, task_, 
                                                pid_ta, thread, pid_m, thread_, 
                                                pid_r, pid_th, ctx, pid_set, 
                                                next_ctx_, pid_y, next_ctx, 
                                                current_ctx_, pid_yi, task_y, 
                                                next_thread, current_ctx, 
                                                pid_ru, task_r, pid_f, task_f, 
                                                pid_pr, pid, current_task, 
                                                next_task, next_thread_, task >>

re_schedule_yield_and_pool(self) == /\ pc[self] = "re_schedule_yield_and_pool"
                                    /\ /\ pid_r' = [pid_r EXCEPT ![self] = pid_y[self]]
                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "re_schedule",
                                                                                pc        |->  "end_yield_and_pool",
                                                                                pid_r     |->  pid_r[self] ] >>
                                                                            \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "lock_preempted_re_schedule"]
                                    /\ UNCHANGED << queue, lock_info, 
                                                    lock_future, 
                                                    lock_scheduler, 
                                                    lock_THREADS, 
                                                    lock_THREAD_POOL, 
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
                                                    thread_index, stored_ctx, 
                                                    stored_task, 
                                                    thread_to_task, 
                                                    task_to_thread, exec_state, 
                                                    thread_is_new, 
                                                    preemption_done, task_w, 
                                                    task_wa, pid_, head_, 
                                                    pid_s, head, pid_g, pid_t, 
                                                    pid_se, ctx_, pid_p, ctx_p, 
                                                    pid_w, task_, pid_ta, 
                                                    thread, pid_m, thread_, 
                                                    pid_th, ctx, pid_set, 
                                                    next_ctx_, pid_y, next_ctx, 
                                                    current_ctx_, pid_yi, 
                                                    task_y, next_thread, 
                                                    current_ctx, pid_ru, 
                                                    task_r, pid_f, task_f, 
                                                    pid_pr, pid, current_task, 
                                                    next_task, next_thread_, 
                                                    task >>

end_yield_and_pool(self) == /\ pc[self] = "end_yield_and_pool"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ current_ctx_' = [current_ctx_ EXCEPT ![self] = Head(stack[self]).current_ctx_]
                            /\ pid_y' = [pid_y EXCEPT ![self] = Head(stack[self]).pid_y]
                            /\ next_ctx' = [next_ctx EXCEPT ![self] = Head(stack[self]).next_ctx]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, lock_THREADS, 
                                            lock_THREAD_POOL, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, state, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREADS_running, 
                                            THREAD_POOL, PREEMPTED_TASKS, 
                                            NEXT_TASK, thread_index, 
                                            stored_ctx, stored_task, 
                                            thread_to_task, task_to_thread, 
                                            exec_state, thread_is_new, 
                                            preemption_done, task_w, task_wa, 
                                            pid_, head_, pid_s, head, pid_g, 
                                            pid_t, pid_se, ctx_, pid_p, ctx_p, 
                                            pid_w, task_, pid_ta, thread, 
                                            pid_m, thread_, pid_r, pid_th, ctx, 
                                            pid_set, next_ctx_, pid_yi, task_y, 
                                            next_thread, current_ctx, pid_ru, 
                                            task_r, pid_f, task_f, pid_pr, pid, 
                                            current_task, next_task, 
                                            next_thread_, task >>

yield_and_pool(self) == start_yield_and_pool(self)
                           \/ lock_result_yield_and_pool(self)
                           \/ get_ctx_yield_and_pool(self)
                           \/ unlock_result_yield_and_pool(self)
                           \/ push_ctx_yield_and_pool(self)
                           \/ context_switch_yield_and_pool(self)
                           \/ set_ctx_yield_and_pool(self)
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
                                                                   /\ pc' = [pc EXCEPT ![self] = "set_ctx_yield_preempted_and_wake_task"]
                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "lock_result_yield_preempted_and_wake_task"]
                                                                   /\ UNCHANGED << exec_state, 
                                                                                   task_y, 
                                                                                   current_ctx >>
                                             /\ UNCHANGED << queue, lock_info, 
                                                             lock_future, 
                                                             lock_scheduler, 
                                                             lock_THREADS, 
                                                             lock_THREAD_POOL, 
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
                                                             stored_ctx, 
                                                             stored_task, 
                                                             thread_to_task, 
                                                             task_to_thread, 
                                                             thread_is_new, 
                                                             preemption_done, 
                                                             stack, task_w, 
                                                             task_wa, pid_, 
                                                             head_, pid_s, 
                                                             head, pid_g, 
                                                             pid_t, pid_se, 
                                                             ctx_, pid_p, 
                                                             ctx_p, pid_w, 
                                                             task_, pid_ta, 
                                                             thread, pid_m, 
                                                             thread_, pid_r, 
                                                             pid_th, ctx, 
                                                             pid_set, 
                                                             next_ctx_, pid_y, 
                                                             next_ctx, 
                                                             current_ctx_, 
                                                             pid_yi, 
                                                             next_thread, 
                                                             pid_ru, task_r, 
                                                             pid_f, task_f, 
                                                             pid_pr, pid, 
                                                             current_task, 
                                                             next_task, 
                                                             next_thread_, 
                                                             task >>

lock_result_yield_preempted_and_wake_task(self) == /\ pc[self] = "lock_result_yield_preempted_and_wake_task"
                                                   /\ ~lock_result_context
                                                   /\ lock_result_context' = TRUE
                                                   /\ pc' = [pc EXCEPT ![self] = "get_ctx_yield_preempted_and_wake_task"]
                                                   /\ UNCHANGED << queue, 
                                                                   lock_info, 
                                                                   lock_future, 
                                                                   lock_scheduler, 
                                                                   lock_THREADS, 
                                                                   lock_THREAD_POOL, 
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
                                                                   stored_ctx, 
                                                                   stored_task, 
                                                                   thread_to_task, 
                                                                   task_to_thread, 
                                                                   exec_state, 
                                                                   thread_is_new, 
                                                                   preemption_done, 
                                                                   stack, 
                                                                   task_w, 
                                                                   task_wa, 
                                                                   pid_, head_, 
                                                                   pid_s, head, 
                                                                   pid_g, 
                                                                   pid_t, 
                                                                   pid_se, 
                                                                   ctx_, pid_p, 
                                                                   ctx_p, 
                                                                   pid_w, 
                                                                   task_, 
                                                                   pid_ta, 
                                                                   thread, 
                                                                   pid_m, 
                                                                   thread_, 
                                                                   pid_r, 
                                                                   pid_th, ctx, 
                                                                   pid_set, 
                                                                   next_ctx_, 
                                                                   pid_y, 
                                                                   next_ctx, 
                                                                   current_ctx_, 
                                                                   pid_yi, 
                                                                   task_y, 
                                                                   next_thread, 
                                                                   current_ctx, 
                                                                   pid_ru, 
                                                                   task_r, 
                                                                   pid_f, 
                                                                   task_f, 
                                                                   pid_pr, pid, 
                                                                   current_task, 
                                                                   next_task, 
                                                                   next_thread_, 
                                                                   task >>

get_ctx_yield_preempted_and_wake_task(self) == /\ pc[self] = "get_ctx_yield_preempted_and_wake_task"
                                               /\ /\ pid_t' = [pid_t EXCEPT ![self] = pid_yi[self]]
                                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "take_current_context",
                                                                                           pc        |->  "unlock_result_yield_preempted_and_wake_task",
                                                                                           pid_t     |->  pid_t[self] ] >>
                                                                                       \o stack[self]]
                                               /\ pc' = [pc EXCEPT ![self] = "wait_take_current_context"]
                                               /\ UNCHANGED << queue, 
                                                               lock_info, 
                                                               lock_future, 
                                                               lock_scheduler, 
                                                               lock_THREADS, 
                                                               lock_THREAD_POOL, 
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
                                                               stored_ctx, 
                                                               stored_task, 
                                                               thread_to_task, 
                                                               task_to_thread, 
                                                               exec_state, 
                                                               thread_is_new, 
                                                               preemption_done, 
                                                               task_w, task_wa, 
                                                               pid_, head_, 
                                                               pid_s, head, 
                                                               pid_g, pid_se, 
                                                               ctx_, pid_p, 
                                                               ctx_p, pid_w, 
                                                               task_, pid_ta, 
                                                               thread, pid_m, 
                                                               thread_, pid_r, 
                                                               pid_th, ctx, 
                                                               pid_set, 
                                                               next_ctx_, 
                                                               pid_y, next_ctx, 
                                                               current_ctx_, 
                                                               pid_yi, task_y, 
                                                               next_thread, 
                                                               current_ctx, 
                                                               pid_ru, task_r, 
                                                               pid_f, task_f, 
                                                               pid_pr, pid, 
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
                                                                     lock_THREADS, 
                                                                     lock_THREAD_POOL, 
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
                                                                     stored_ctx, 
                                                                     stored_task, 
                                                                     thread_to_task, 
                                                                     task_to_thread, 
                                                                     exec_state, 
                                                                     thread_is_new, 
                                                                     preemption_done, 
                                                                     stack, 
                                                                     task_w, 
                                                                     task_wa, 
                                                                     pid_, 
                                                                     head_, 
                                                                     pid_s, 
                                                                     head, 
                                                                     pid_g, 
                                                                     pid_t, 
                                                                     pid_se, 
                                                                     ctx_, 
                                                                     pid_p, 
                                                                     ctx_p, 
                                                                     pid_w, 
                                                                     task_, 
                                                                     pid_ta, 
                                                                     thread, 
                                                                     pid_m, 
                                                                     thread_, 
                                                                     pid_r, 
                                                                     pid_th, 
                                                                     ctx, 
                                                                     pid_set, 
                                                                     next_ctx_, 
                                                                     pid_y, 
                                                                     next_ctx, 
                                                                     current_ctx_, 
                                                                     pid_yi, 
                                                                     task_y, 
                                                                     next_thread, 
                                                                     pid_ru, 
                                                                     task_r, 
                                                                     pid_f, 
                                                                     task_f, 
                                                                     pid_pr, 
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
                                                                 lock_THREADS, 
                                                                 lock_THREAD_POOL, 
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
                                                                 stored_ctx, 
                                                                 stored_task, 
                                                                 thread_to_task, 
                                                                 task_to_thread, 
                                                                 exec_state, 
                                                                 thread_is_new, 
                                                                 preemption_done, 
                                                                 stack, task_w, 
                                                                 task_wa, pid_, 
                                                                 head_, pid_s, 
                                                                 head, pid_g, 
                                                                 pid_t, pid_se, 
                                                                 ctx_, pid_p, 
                                                                 ctx_p, pid_w, 
                                                                 task_, pid_ta, 
                                                                 thread, pid_m, 
                                                                 thread_, 
                                                                 pid_r, pid_th, 
                                                                 ctx, pid_set, 
                                                                 next_ctx_, 
                                                                 pid_y, 
                                                                 next_ctx, 
                                                                 current_ctx_, 
                                                                 pid_yi, 
                                                                 task_y, 
                                                                 next_thread, 
                                                                 current_ctx, 
                                                                 pid_ru, 
                                                                 task_r, pid_f, 
                                                                 task_f, 
                                                                 pid_pr, pid, 
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
                                                                     lock_THREADS, 
                                                                     lock_THREAD_POOL, 
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
                                                                     stored_ctx, 
                                                                     stored_task, 
                                                                     exec_state, 
                                                                     thread_is_new, 
                                                                     preemption_done, 
                                                                     stack, 
                                                                     task_w, 
                                                                     task_wa, 
                                                                     pid_, 
                                                                     head_, 
                                                                     pid_s, 
                                                                     head, 
                                                                     pid_g, 
                                                                     pid_t, 
                                                                     pid_se, 
                                                                     ctx_, 
                                                                     pid_p, 
                                                                     ctx_p, 
                                                                     pid_w, 
                                                                     task_, 
                                                                     pid_ta, 
                                                                     thread, 
                                                                     pid_m, 
                                                                     thread_, 
                                                                     pid_r, 
                                                                     pid_th, 
                                                                     ctx, 
                                                                     pid_set, 
                                                                     next_ctx_, 
                                                                     pid_y, 
                                                                     next_ctx, 
                                                                     current_ctx_, 
                                                                     pid_yi, 
                                                                     task_y, 
                                                                     next_thread, 
                                                                     current_ctx, 
                                                                     pid_ru, 
                                                                     task_r, 
                                                                     pid_f, 
                                                                     task_f, 
                                                                     pid_pr, 
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
                                                                 lock_THREADS, 
                                                                 lock_THREAD_POOL, 
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
                                                                 stored_ctx, 
                                                                 stored_task, 
                                                                 thread_to_task, 
                                                                 task_to_thread, 
                                                                 exec_state, 
                                                                 thread_is_new, 
                                                                 preemption_done, 
                                                                 stack, task_w, 
                                                                 task_wa, pid_, 
                                                                 head_, pid_s, 
                                                                 head, pid_g, 
                                                                 pid_t, pid_se, 
                                                                 ctx_, pid_p, 
                                                                 ctx_p, pid_w, 
                                                                 task_, pid_ta, 
                                                                 thread, pid_m, 
                                                                 thread_, 
                                                                 pid_r, pid_th, 
                                                                 ctx, pid_set, 
                                                                 next_ctx_, 
                                                                 pid_y, 
                                                                 next_ctx, 
                                                                 current_ctx_, 
                                                                 pid_yi, 
                                                                 task_y, 
                                                                 next_thread, 
                                                                 current_ctx, 
                                                                 pid_ru, 
                                                                 task_r, pid_f, 
                                                                 task_f, 
                                                                 pid_pr, pid, 
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
                                                                      lock_THREADS, 
                                                                      lock_THREAD_POOL, 
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
                                                                      stored_ctx, 
                                                                      stored_task, 
                                                                      thread_to_task, 
                                                                      task_to_thread, 
                                                                      exec_state, 
                                                                      thread_is_new, 
                                                                      preemption_done, 
                                                                      stack, 
                                                                      task_w, 
                                                                      task_wa, 
                                                                      pid_, 
                                                                      head_, 
                                                                      pid_s, 
                                                                      head, 
                                                                      pid_g, 
                                                                      pid_t, 
                                                                      pid_se, 
                                                                      ctx_, 
                                                                      pid_p, 
                                                                      ctx_p, 
                                                                      pid_w, 
                                                                      task_, 
                                                                      pid_ta, 
                                                                      thread, 
                                                                      pid_m, 
                                                                      thread_, 
                                                                      pid_r, 
                                                                      pid_th, 
                                                                      ctx, 
                                                                      pid_set, 
                                                                      next_ctx_, 
                                                                      pid_y, 
                                                                      next_ctx, 
                                                                      current_ctx_, 
                                                                      pid_yi, 
                                                                      task_y, 
                                                                      next_thread, 
                                                                      current_ctx, 
                                                                      pid_ru, 
                                                                      task_r, 
                                                                      pid_f, 
                                                                      task_f, 
                                                                      pid_pr, 
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
                                                                 lock_THREADS, 
                                                                 lock_THREAD_POOL, 
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
                                                                 stored_ctx, 
                                                                 stored_task, 
                                                                 thread_to_task, 
                                                                 task_to_thread, 
                                                                 exec_state, 
                                                                 thread_is_new, 
                                                                 preemption_done, 
                                                                 stack, task_w, 
                                                                 task_wa, pid_, 
                                                                 head_, pid_s, 
                                                                 head, pid_g, 
                                                                 pid_t, pid_se, 
                                                                 ctx_, pid_p, 
                                                                 ctx_p, pid_w, 
                                                                 task_, pid_ta, 
                                                                 thread, pid_m, 
                                                                 thread_, 
                                                                 pid_r, pid_th, 
                                                                 ctx, pid_set, 
                                                                 next_ctx_, 
                                                                 pid_y, 
                                                                 next_ctx, 
                                                                 current_ctx_, 
                                                                 pid_yi, 
                                                                 task_y, 
                                                                 next_thread, 
                                                                 current_ctx, 
                                                                 pid_ru, 
                                                                 task_r, pid_f, 
                                                                 task_f, 
                                                                 pid_pr, pid, 
                                                                 current_task, 
                                                                 next_task, 
                                                                 next_thread_, 
                                                                 task >>

context_switch_yield_preempted_and_wake_task(self) == /\ pc[self] = "context_switch_yield_preempted_and_wake_task"
                                                      /\ stored_task' = [stored_task EXCEPT ![pid_yi[self]] = thread_to_task[next_thread[self]]]
                                                      /\ stored_ctx' = [stored_ctx EXCEPT ![pid_yi[self]] = next_thread[self]]
                                                      /\ /\ current_ctx' = [current_ctx EXCEPT ![self] = Head(stack[self]).current_ctx]
                                                         /\ next_ctx_' = [next_ctx_ EXCEPT ![self] = next_thread[self]]
                                                         /\ pid_set' = [pid_set EXCEPT ![self] = pid_yi[self]]
                                                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_exec_state",
                                                                                                  pc        |->  Head(stack[self]).pc,
                                                                                                  pid_set   |->  pid_set[self],
                                                                                                  next_ctx_ |->  next_ctx_[self] ] >>
                                                                                              \o Tail(stack[self])]
                                                      /\ pc' = [pc EXCEPT ![self] = "start_set_exec_state"]
                                                      /\ UNCHANGED << queue, 
                                                                      lock_info, 
                                                                      lock_future, 
                                                                      lock_scheduler, 
                                                                      lock_THREADS, 
                                                                      lock_THREAD_POOL, 
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
                                                                      thread_to_task, 
                                                                      task_to_thread, 
                                                                      exec_state, 
                                                                      thread_is_new, 
                                                                      preemption_done, 
                                                                      task_w, 
                                                                      task_wa, 
                                                                      pid_, 
                                                                      head_, 
                                                                      pid_s, 
                                                                      head, 
                                                                      pid_g, 
                                                                      pid_t, 
                                                                      pid_se, 
                                                                      ctx_, 
                                                                      pid_p, 
                                                                      ctx_p, 
                                                                      pid_w, 
                                                                      task_, 
                                                                      pid_ta, 
                                                                      thread, 
                                                                      pid_m, 
                                                                      thread_, 
                                                                      pid_r, 
                                                                      pid_th, 
                                                                      ctx, 
                                                                      pid_y, 
                                                                      next_ctx, 
                                                                      current_ctx_, 
                                                                      pid_yi, 
                                                                      task_y, 
                                                                      next_thread, 
                                                                      pid_ru, 
                                                                      task_r, 
                                                                      pid_f, 
                                                                      task_f, 
                                                                      pid_pr, 
                                                                      pid, 
                                                                      current_task, 
                                                                      next_task, 
                                                                      next_thread_, 
                                                                      task >>

set_ctx_yield_preempted_and_wake_task(self) == /\ pc[self] = "set_ctx_yield_preempted_and_wake_task"
                                               /\ /\ ctx_' = [ctx_ EXCEPT ![self] = current_ctx[self]]
                                                  /\ pid_se' = [pid_se EXCEPT ![self] = pid_yi[self]]
                                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_current_context",
                                                                                           pc        |->  "re_schedule_yield_preempted_and_wake_task",
                                                                                           pid_se    |->  pid_se[self],
                                                                                           ctx_      |->  ctx_[self] ] >>
                                                                                       \o stack[self]]
                                               /\ pc' = [pc EXCEPT ![self] = "wait_set_current_context"]
                                               /\ UNCHANGED << queue, 
                                                               lock_info, 
                                                               lock_future, 
                                                               lock_scheduler, 
                                                               lock_THREADS, 
                                                               lock_THREAD_POOL, 
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
                                                               stored_ctx, 
                                                               stored_task, 
                                                               thread_to_task, 
                                                               task_to_thread, 
                                                               exec_state, 
                                                               thread_is_new, 
                                                               preemption_done, 
                                                               task_w, task_wa, 
                                                               pid_, head_, 
                                                               pid_s, head, 
                                                               pid_g, pid_t, 
                                                               pid_p, ctx_p, 
                                                               pid_w, task_, 
                                                               pid_ta, thread, 
                                                               pid_m, thread_, 
                                                               pid_r, pid_th, 
                                                               ctx, pid_set, 
                                                               next_ctx_, 
                                                               pid_y, next_ctx, 
                                                               current_ctx_, 
                                                               pid_yi, task_y, 
                                                               next_thread, 
                                                               current_ctx, 
                                                               pid_ru, task_r, 
                                                               pid_f, task_f, 
                                                               pid_pr, pid, 
                                                               current_task, 
                                                               next_task, 
                                                               next_thread_, 
                                                               task >>

re_schedule_yield_preempted_and_wake_task(self) == /\ pc[self] = "re_schedule_yield_preempted_and_wake_task"
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
                                                                   lock_THREADS, 
                                                                   lock_THREAD_POOL, 
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
                                                                   stored_ctx, 
                                                                   stored_task, 
                                                                   thread_to_task, 
                                                                   task_to_thread, 
                                                                   exec_state, 
                                                                   thread_is_new, 
                                                                   preemption_done, 
                                                                   task_w, 
                                                                   task_wa, 
                                                                   pid_, head_, 
                                                                   pid_s, head, 
                                                                   pid_g, 
                                                                   pid_t, 
                                                                   pid_se, 
                                                                   ctx_, pid_p, 
                                                                   ctx_p, 
                                                                   pid_w, 
                                                                   task_, 
                                                                   pid_ta, 
                                                                   thread, 
                                                                   pid_m, 
                                                                   thread_, 
                                                                   pid_th, ctx, 
                                                                   pid_set, 
                                                                   next_ctx_, 
                                                                   pid_y, 
                                                                   next_ctx, 
                                                                   current_ctx_, 
                                                                   pid_yi, 
                                                                   task_y, 
                                                                   next_thread, 
                                                                   current_ctx, 
                                                                   pid_ru, 
                                                                   task_r, 
                                                                   pid_f, 
                                                                   task_f, 
                                                                   pid_pr, pid, 
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
                                                           lock_THREADS, 
                                                           lock_THREAD_POOL, 
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
                                                           stored_ctx, 
                                                           stored_task, 
                                                           thread_to_task, 
                                                           task_to_thread, 
                                                           exec_state, 
                                                           thread_is_new, 
                                                           preemption_done, 
                                                           task_w, task_wa, 
                                                           pid_, head_, pid_s, 
                                                           head, pid_g, pid_t, 
                                                           pid_se, ctx_, pid_p, 
                                                           ctx_p, pid_w, task_, 
                                                           pid_ta, thread, 
                                                           pid_m, thread_, 
                                                           pid_r, pid_th, ctx, 
                                                           pid_set, next_ctx_, 
                                                           pid_y, next_ctx, 
                                                           current_ctx_, 
                                                           pid_ru, task_r, 
                                                           pid_f, task_f, 
                                                           pid_pr, pid, 
                                                           current_task, 
                                                           next_task, 
                                                           next_thread_, task >>

yield_preempted_and_wake_task(self) == start_yield_preempted_and_wake_task(self)
                                          \/ lock_result_yield_preempted_and_wake_task(self)
                                          \/ get_ctx_yield_preempted_and_wake_task(self)
                                          \/ unlock_result_yield_preempted_and_wake_task(self)
                                          \/ lock_task_yield_preempted_and_wake_task(self)
                                          \/ set_preempted_yield_preempted_and_wake_task(self)
                                          \/ set_state_yield_preempted_and_wake_task(self)
                                          \/ lock_preempted_yield_preempted_and_wake_task(self)
                                          \/ push_task_yield_preempted_and_wake_task(self)
                                          \/ context_switch_yield_preempted_and_wake_task(self)
                                          \/ set_ctx_yield_preempted_and_wake_task(self)
                                          \/ re_schedule_yield_preempted_and_wake_task(self)
                                          \/ end_yield_preempted_and_wake_task(self)

start_run_main(self) == /\ pc[self] = "start_run_main"
                        /\ IF exec_state[pid_ru[self]] = "Init"
                              THEN /\ pc' = [pc EXCEPT ![self] = "get_next_run_main"]
                                   /\ UNCHANGED << preemption_done, task_r >>
                              ELSE /\ IF exec_state[pid_ru[self]] = "Yielded"
                                         THEN /\ task_r' = [task_r EXCEPT ![self] = stored_task[pid_ru[self]]]
                                              /\ pc' = [pc EXCEPT ![self] = "yield_run_main"]
                                              /\ UNCHANGED preemption_done
                                         ELSE /\ IF exec_state[pid_ru[self]] = "Preempted"
                                                    THEN /\ task_r' = [task_r EXCEPT ![self] = stored_task[pid_ru[self]]]
                                                         /\ preemption_done' = preemption_done - 1
                                                         /\ pc' = [pc EXCEPT ![self] = "preempt_run_main"]
                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "get_next_run_main"]
                                                         /\ UNCHANGED << preemption_done, 
                                                                         task_r >>
                        /\ UNCHANGED << queue, lock_info, lock_future, 
                                        lock_scheduler, lock_THREADS, 
                                        lock_THREAD_POOL, lock_PREEMPTED_TASKS, 
                                        lock_NEXT_TASK, lock_result_context, 
                                        in_queue, need_sched, state, 
                                        result_next, result_future, 
                                        result_context, result_thread, RUNNING, 
                                        THREADS_pooled, THREADS_running, 
                                        THREAD_POOL, PREEMPTED_TASKS, 
                                        NEXT_TASK, thread_index, stored_ctx, 
                                        stored_task, thread_to_task, 
                                        task_to_thread, exec_state, 
                                        thread_is_new, stack, task_w, task_wa, 
                                        pid_, head_, pid_s, head, pid_g, pid_t, 
                                        pid_se, ctx_, pid_p, ctx_p, pid_w, 
                                        task_, pid_ta, thread, pid_m, thread_, 
                                        pid_r, pid_th, ctx, pid_set, next_ctx_, 
                                        pid_y, next_ctx, current_ctx_, pid_yi, 
                                        task_y, next_thread, current_ctx, 
                                        pid_ru, pid_f, task_f, pid_pr, pid, 
                                        current_task, next_task, next_thread_, 
                                        task >>

get_next_run_main(self) == /\ pc[self] = "get_next_run_main"
                           /\ /\ pid_g' = [pid_g EXCEPT ![self] = pid_ru[self]]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "get_next_task",
                                                                       pc        |->  "get_task_run_main",
                                                                       pid_g     |->  pid_g[self] ] >>
                                                                   \o stack[self]]
                           /\ pc' = [pc EXCEPT ![self] = "preempt_get_next_task_"]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, lock_THREADS, 
                                           lock_THREAD_POOL, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, stored_ctx, 
                                           stored_task, thread_to_task, 
                                           task_to_thread, exec_state, 
                                           thread_is_new, preemption_done, 
                                           task_w, task_wa, pid_, head_, pid_s, 
                                           head, pid_t, pid_se, ctx_, pid_p, 
                                           ctx_p, pid_w, task_, pid_ta, thread, 
                                           pid_m, thread_, pid_r, pid_th, ctx, 
                                           pid_set, next_ctx_, pid_y, next_ctx, 
                                           current_ctx_, pid_yi, task_y, 
                                           next_thread, current_ctx, pid_ru, 
                                           task_r, pid_f, task_f, pid_pr, pid, 
                                           current_task, next_task, 
                                           next_thread_, task >>

get_task_run_main(self) == /\ pc[self] = "get_task_run_main"
                           /\ task_r' = [task_r EXCEPT ![self] = result_next[pid_ru[self]]]
                           /\ IF task_r'[self] < 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "lock_task_run_main"]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, lock_THREADS, 
                                           lock_THREAD_POOL, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, stored_ctx, 
                                           stored_task, thread_to_task, 
                                           task_to_thread, exec_state, 
                                           thread_is_new, preemption_done, 
                                           stack, task_w, task_wa, pid_, head_, 
                                           pid_s, head, pid_g, pid_t, pid_se, 
                                           ctx_, pid_p, ctx_p, pid_w, task_, 
                                           pid_ta, thread, pid_m, thread_, 
                                           pid_r, pid_th, ctx, pid_set, 
                                           next_ctx_, pid_y, next_ctx, 
                                           current_ctx_, pid_yi, task_y, 
                                           next_thread, current_ctx, pid_ru, 
                                           pid_f, task_f, pid_pr, pid, 
                                           current_task, next_task, 
                                           next_thread_, task >>

lock_task_run_main(self) == /\ pc[self] = "lock_task_run_main"
                            /\ ~lock_info[task_r[self]]
                            /\ lock_info' = [lock_info EXCEPT ![task_r[self]] = TRUE]
                            /\ IF task_to_thread[task_r[self]] > 0
                                  THEN /\ state' = [state EXCEPT ![task_r[self]] = "Running"]
                                       /\ pc' = [pc EXCEPT ![self] = "yield_run_main"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "unlock_task_run_main"]
                                       /\ state' = state
                            /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                            lock_THREADS, lock_THREAD_POOL, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREADS_running, 
                                            THREAD_POOL, PREEMPTED_TASKS, 
                                            NEXT_TASK, thread_index, 
                                            stored_ctx, stored_task, 
                                            thread_to_task, task_to_thread, 
                                            exec_state, thread_is_new, 
                                            preemption_done, stack, task_w, 
                                            task_wa, pid_, head_, pid_s, head, 
                                            pid_g, pid_t, pid_se, ctx_, pid_p, 
                                            ctx_p, pid_w, task_, pid_ta, 
                                            thread, pid_m, thread_, pid_r, 
                                            pid_th, ctx, pid_set, next_ctx_, 
                                            pid_y, next_ctx, current_ctx_, 
                                            pid_yi, task_y, next_thread, 
                                            current_ctx, pid_ru, task_r, pid_f, 
                                            task_f, pid_pr, pid, current_task, 
                                            next_task, next_thread_, task >>

yield_run_main(self) == /\ pc[self] = "yield_run_main"
                        /\ /\ next_ctx' = [next_ctx EXCEPT ![self] = task_r[self]]
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
                                        lock_scheduler, lock_THREADS, 
                                        lock_THREAD_POOL, lock_PREEMPTED_TASKS, 
                                        lock_NEXT_TASK, lock_result_context, 
                                        in_queue, need_sched, state, 
                                        result_next, result_future, 
                                        result_context, result_thread, RUNNING, 
                                        THREADS_pooled, THREADS_running, 
                                        THREAD_POOL, PREEMPTED_TASKS, 
                                        NEXT_TASK, thread_index, stored_ctx, 
                                        stored_task, thread_to_task, 
                                        task_to_thread, exec_state, 
                                        thread_is_new, preemption_done, task_w, 
                                        task_wa, pid_, head_, pid_s, head, 
                                        pid_g, pid_t, pid_se, ctx_, pid_p, 
                                        ctx_p, pid_w, task_, pid_ta, thread, 
                                        pid_m, thread_, pid_r, pid_th, ctx, 
                                        pid_set, next_ctx_, pid_yi, task_y, 
                                        next_thread, current_ctx, pid_ru, 
                                        task_r, pid_f, task_f, pid_pr, pid, 
                                        current_task, next_task, next_thread_, 
                                        task >>

continue_run_main(self) == /\ pc[self] = "continue_run_main"
                           /\ lock_info' = [lock_info EXCEPT ![task_r[self]] = FALSE]
                           /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                           /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                           lock_THREADS, lock_THREAD_POOL, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, stored_ctx, 
                                           stored_task, thread_to_task, 
                                           task_to_thread, exec_state, 
                                           thread_is_new, preemption_done, 
                                           stack, task_w, task_wa, pid_, head_, 
                                           pid_s, head, pid_g, pid_t, pid_se, 
                                           ctx_, pid_p, ctx_p, pid_w, task_, 
                                           pid_ta, thread, pid_m, thread_, 
                                           pid_r, pid_th, ctx, pid_set, 
                                           next_ctx_, pid_y, next_ctx, 
                                           current_ctx_, pid_yi, task_y, 
                                           next_thread, current_ctx, pid_ru, 
                                           task_r, pid_f, task_f, pid_pr, pid, 
                                           current_task, next_task, 
                                           next_thread_, task >>

unlock_task_run_main(self) == /\ pc[self] = "unlock_task_run_main"
                              /\ lock_info' = [lock_info EXCEPT ![task_r[self]] = FALSE]
                              /\ pc' = [pc EXCEPT ![self] = "lock_future_run_main"]
                              /\ UNCHANGED << queue, lock_future, 
                                              lock_scheduler, lock_THREADS, 
                                              lock_THREAD_POOL, 
                                              lock_PREEMPTED_TASKS, 
                                              lock_NEXT_TASK, 
                                              lock_result_context, in_queue, 
                                              need_sched, state, result_next, 
                                              result_future, result_context, 
                                              result_thread, RUNNING, 
                                              THREADS_pooled, THREADS_running, 
                                              THREAD_POOL, PREEMPTED_TASKS, 
                                              NEXT_TASK, thread_index, 
                                              stored_ctx, stored_task, 
                                              thread_to_task, task_to_thread, 
                                              exec_state, thread_is_new, 
                                              preemption_done, stack, task_w, 
                                              task_wa, pid_, head_, pid_s, 
                                              head, pid_g, pid_t, pid_se, ctx_, 
                                              pid_p, ctx_p, pid_w, task_, 
                                              pid_ta, thread, pid_m, thread_, 
                                              pid_r, pid_th, ctx, pid_set, 
                                              next_ctx_, pid_y, next_ctx, 
                                              current_ctx_, pid_yi, task_y, 
                                              next_thread, current_ctx, pid_ru, 
                                              task_r, pid_f, task_f, pid_pr, 
                                              pid, current_task, next_task, 
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
                                              lock_THREADS, lock_THREAD_POOL, 
                                              lock_PREEMPTED_TASKS, 
                                              lock_NEXT_TASK, 
                                              lock_result_context, in_queue, 
                                              need_sched, state, result_next, 
                                              result_future, result_context, 
                                              result_thread, RUNNING, 
                                              THREADS_pooled, THREADS_running, 
                                              THREAD_POOL, PREEMPTED_TASKS, 
                                              NEXT_TASK, thread_index, 
                                              stored_ctx, stored_task, 
                                              thread_to_task, task_to_thread, 
                                              exec_state, thread_is_new, 
                                              preemption_done, task_w, pid_, 
                                              head_, pid_s, head, pid_g, pid_t, 
                                              pid_se, ctx_, pid_p, ctx_p, 
                                              pid_w, task_, pid_ta, thread, 
                                              pid_m, thread_, pid_r, pid_th, 
                                              ctx, pid_set, next_ctx_, pid_y, 
                                              next_ctx, current_ctx_, pid_yi, 
                                              task_y, next_thread, current_ctx, 
                                              pid_ru, task_r, pid_f, task_f, 
                                              pid_pr, pid, current_task, 
                                              next_task, next_thread_, task >>

check_run_main(self) == /\ pc[self] = "check_run_main"
                        /\ ~lock_info[task_r[self]]
                        /\ lock_info' = [lock_info EXCEPT ![task_r[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = "terminated_run_main"]
                        /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                        lock_THREADS, lock_THREAD_POOL, 
                                        lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                        lock_result_context, in_queue, 
                                        need_sched, state, result_next, 
                                        result_future, result_context, 
                                        result_thread, RUNNING, THREADS_pooled, 
                                        THREADS_running, THREAD_POOL, 
                                        PREEMPTED_TASKS, NEXT_TASK, 
                                        thread_index, stored_ctx, stored_task, 
                                        thread_to_task, task_to_thread, 
                                        exec_state, thread_is_new, 
                                        preemption_done, stack, task_w, 
                                        task_wa, pid_, head_, pid_s, head, 
                                        pid_g, pid_t, pid_se, ctx_, pid_p, 
                                        ctx_p, pid_w, task_, pid_ta, thread, 
                                        pid_m, thread_, pid_r, pid_th, ctx, 
                                        pid_set, next_ctx_, pid_y, next_ctx, 
                                        current_ctx_, pid_yi, task_y, 
                                        next_thread, current_ctx, pid_ru, 
                                        task_r, pid_f, task_f, pid_pr, pid, 
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
                                             lock_THREADS, lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, thread_is_new, 
                                             preemption_done, stack, task_w, 
                                             task_wa, pid_, head_, pid_s, head, 
                                             pid_g, pid_t, pid_se, ctx_, pid_p, 
                                             ctx_p, pid_w, task_, pid_ta, 
                                             thread, pid_m, thread_, pid_r, 
                                             pid_th, ctx, pid_set, next_ctx_, 
                                             pid_y, next_ctx, current_ctx_, 
                                             pid_yi, task_y, next_thread, 
                                             current_ctx, pid_ru, task_r, 
                                             pid_f, task_f, pid_pr, pid, 
                                             current_task, next_task, 
                                             next_thread_, task >>

pre_future_run_main(self) == /\ pc[self] = "pre_future_run_main"
                             /\ state' = [state EXCEPT ![task_r[self]] = "Running"]
                             /\ need_sched' = [need_sched EXCEPT ![task_r[self]] = FALSE]
                             /\ lock_info' = [lock_info EXCEPT ![task_r[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = "set_task_run_main"]
                             /\ UNCHANGED << queue, lock_future, 
                                             lock_scheduler, lock_THREADS, 
                                             lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             result_next, result_future, 
                                             result_context, result_thread, 
                                             RUNNING, THREADS_pooled, 
                                             THREADS_running, THREAD_POOL, 
                                             PREEMPTED_TASKS, NEXT_TASK, 
                                             thread_index, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             thread_is_new, preemption_done, 
                                             stack, task_w, task_wa, pid_, 
                                             head_, pid_s, head, pid_g, pid_t, 
                                             pid_se, ctx_, pid_p, ctx_p, pid_w, 
                                             task_, pid_ta, thread, pid_m, 
                                             thread_, pid_r, pid_th, ctx, 
                                             pid_set, next_ctx_, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, pid_f, task_f, 
                                             pid_pr, pid, current_task, 
                                             next_task, next_thread_, task >>

set_task_run_main(self) == /\ pc[self] = "set_task_run_main"
                           /\ RUNNING' = [RUNNING EXCEPT ![pid_ru[self]] = task_r[self]]
                           /\ pc' = [pc EXCEPT ![self] = "preempt_run_main"]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, lock_THREADS, 
                                           lock_THREAD_POOL, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           THREADS_pooled, THREADS_running, 
                                           THREAD_POOL, PREEMPTED_TASKS, 
                                           NEXT_TASK, thread_index, stored_ctx, 
                                           stored_task, thread_to_task, 
                                           task_to_thread, exec_state, 
                                           thread_is_new, preemption_done, 
                                           stack, task_w, task_wa, pid_, head_, 
                                           pid_s, head, pid_g, pid_t, pid_se, 
                                           ctx_, pid_p, ctx_p, pid_w, task_, 
                                           pid_ta, thread, pid_m, thread_, 
                                           pid_r, pid_th, ctx, pid_set, 
                                           next_ctx_, pid_y, next_ctx, 
                                           current_ctx_, pid_yi, task_y, 
                                           next_thread, current_ctx, pid_ru, 
                                           task_r, pid_f, task_f, pid_pr, pid, 
                                           current_task, next_task, 
                                           next_thread_, task >>

preempt_run_main(self) == /\ pc[self] = "preempt_run_main"
                          /\ IF preemption_done < 0
                                THEN /\ preemption_done' = preemption_done + 1
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
                                ELSE /\ pc' = [pc EXCEPT ![self] = "start_future_run_main"]
                                     /\ UNCHANGED << preemption_done, stack, 
                                                     pid, current_task, 
                                                     next_task, next_thread_ >>
                          /\ UNCHANGED << queue, lock_info, lock_future, 
                                          lock_scheduler, lock_THREADS, 
                                          lock_THREAD_POOL, 
                                          lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                          lock_result_context, in_queue, 
                                          need_sched, state, result_next, 
                                          result_future, result_context, 
                                          result_thread, RUNNING, 
                                          THREADS_pooled, THREADS_running, 
                                          THREAD_POOL, PREEMPTED_TASKS, 
                                          NEXT_TASK, thread_index, stored_ctx, 
                                          stored_task, thread_to_task, 
                                          task_to_thread, exec_state, 
                                          thread_is_new, task_w, task_wa, pid_, 
                                          head_, pid_s, head, pid_g, pid_t, 
                                          pid_se, ctx_, pid_p, ctx_p, pid_w, 
                                          task_, pid_ta, thread, pid_m, 
                                          thread_, pid_r, pid_th, ctx, pid_set, 
                                          next_ctx_, pid_y, next_ctx, 
                                          current_ctx_, pid_yi, task_y, 
                                          next_thread, current_ctx, pid_ru, 
                                          task_r, pid_f, task_f, pid_pr, task >>

continue_run_main3(self) == /\ pc[self] = "continue_run_main3"
                            /\ IF exec_state[pid_ru[self]] = "Preempted"
                                  THEN /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "start_future_run_main"]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, lock_THREADS, 
                                            lock_THREAD_POOL, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, state, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREADS_running, 
                                            THREAD_POOL, PREEMPTED_TASKS, 
                                            NEXT_TASK, thread_index, 
                                            stored_ctx, stored_task, 
                                            thread_to_task, task_to_thread, 
                                            exec_state, thread_is_new, 
                                            preemption_done, stack, task_w, 
                                            task_wa, pid_, head_, pid_s, head, 
                                            pid_g, pid_t, pid_se, ctx_, pid_p, 
                                            ctx_p, pid_w, task_, pid_ta, 
                                            thread, pid_m, thread_, pid_r, 
                                            pid_th, ctx, pid_set, next_ctx_, 
                                            pid_y, next_ctx, current_ctx_, 
                                            pid_yi, task_y, next_thread, 
                                            current_ctx, pid_ru, task_r, pid_f, 
                                            task_f, pid_pr, pid, current_task, 
                                            next_task, next_thread_, task >>

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
                                               lock_scheduler, lock_THREADS, 
                                               lock_THREAD_POOL, 
                                               lock_PREEMPTED_TASKS, 
                                               lock_NEXT_TASK, 
                                               lock_result_context, in_queue, 
                                               need_sched, state, result_next, 
                                               result_future, result_context, 
                                               result_thread, RUNNING, 
                                               THREADS_pooled, THREADS_running, 
                                               THREAD_POOL, PREEMPTED_TASKS, 
                                               NEXT_TASK, thread_index, 
                                               stored_ctx, stored_task, 
                                               thread_to_task, task_to_thread, 
                                               exec_state, thread_is_new, 
                                               preemption_done, task_w, 
                                               task_wa, pid_, head_, pid_s, 
                                               head, pid_g, pid_t, pid_se, 
                                               ctx_, pid_p, ctx_p, pid_w, 
                                               task_, pid_ta, thread, pid_m, 
                                               thread_, pid_r, pid_th, ctx, 
                                               pid_set, next_ctx_, pid_y, 
                                               next_ctx, current_ctx_, pid_yi, 
                                               task_y, next_thread, 
                                               current_ctx, pid_ru, task_r, 
                                               pid_pr, pid, current_task, 
                                               next_task, next_thread_, task >>

end_future_run_main(self) == /\ pc[self] = "end_future_run_main"
                             /\ lock_future' = [lock_future EXCEPT ![task_r[self]] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = "unset_task_run_main"]
                             /\ UNCHANGED << queue, lock_info, lock_scheduler, 
                                             lock_THREADS, lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, thread_is_new, 
                                             preemption_done, stack, task_w, 
                                             task_wa, pid_, head_, pid_s, head, 
                                             pid_g, pid_t, pid_se, ctx_, pid_p, 
                                             ctx_p, pid_w, task_, pid_ta, 
                                             thread, pid_m, thread_, pid_r, 
                                             pid_th, ctx, pid_set, next_ctx_, 
                                             pid_y, next_ctx, current_ctx_, 
                                             pid_yi, task_y, next_thread, 
                                             current_ctx, pid_ru, task_r, 
                                             pid_f, task_f, pid_pr, pid, 
                                             current_task, next_task, 
                                             next_thread_, task >>

unset_task_run_main(self) == /\ pc[self] = "unset_task_run_main"
                             /\ RUNNING' = [RUNNING EXCEPT ![pid_ru[self]] = -1]
                             /\ pc' = [pc EXCEPT ![self] = "post_future_run_main"]
                             /\ UNCHANGED << queue, lock_info, lock_future, 
                                             lock_scheduler, lock_THREADS, 
                                             lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, THREADS_pooled, 
                                             THREADS_running, THREAD_POOL, 
                                             PREEMPTED_TASKS, NEXT_TASK, 
                                             thread_index, stored_ctx, 
                                             stored_task, thread_to_task, 
                                             task_to_thread, exec_state, 
                                             thread_is_new, preemption_done, 
                                             stack, task_w, task_wa, pid_, 
                                             head_, pid_s, head, pid_g, pid_t, 
                                             pid_se, ctx_, pid_p, ctx_p, pid_w, 
                                             task_, pid_ta, thread, pid_m, 
                                             thread_, pid_r, pid_th, ctx, 
                                             pid_set, next_ctx_, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, pid_f, task_f, 
                                             pid_pr, pid, current_task, 
                                             next_task, next_thread_, task >>

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
                                                              "Failure of assertion at line 582, column 13.")
                                                    /\ state' = state
                                         /\ pc' = [pc EXCEPT ![self] = "continue_run_main2"]
                              /\ UNCHANGED << queue, lock_future, 
                                              lock_scheduler, lock_THREADS, 
                                              lock_THREAD_POOL, 
                                              lock_PREEMPTED_TASKS, 
                                              lock_NEXT_TASK, 
                                              lock_result_context, in_queue, 
                                              need_sched, result_next, 
                                              result_future, result_context, 
                                              result_thread, RUNNING, 
                                              THREADS_pooled, THREADS_running, 
                                              THREAD_POOL, PREEMPTED_TASKS, 
                                              NEXT_TASK, thread_index, 
                                              stored_ctx, stored_task, 
                                              thread_to_task, task_to_thread, 
                                              exec_state, thread_is_new, 
                                              preemption_done, stack, task_w, 
                                              task_wa, pid_, head_, pid_s, 
                                              head, pid_g, pid_t, pid_se, ctx_, 
                                              pid_p, ctx_p, pid_w, task_, 
                                              pid_ta, thread, pid_m, thread_, 
                                              pid_r, pid_th, ctx, pid_set, 
                                              next_ctx_, pid_y, next_ctx, 
                                              current_ctx_, pid_yi, task_y, 
                                              next_thread, current_ctx, pid_ru, 
                                              task_r, pid_f, task_f, pid_pr, 
                                              pid, current_task, next_task, 
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
                                               lock_scheduler, lock_THREADS, 
                                               lock_THREAD_POOL, 
                                               lock_PREEMPTED_TASKS, 
                                               lock_NEXT_TASK, 
                                               lock_result_context, in_queue, 
                                               state, result_next, 
                                               result_future, result_context, 
                                               result_thread, RUNNING, 
                                               THREADS_pooled, THREADS_running, 
                                               THREAD_POOL, PREEMPTED_TASKS, 
                                               NEXT_TASK, thread_index, 
                                               stored_ctx, stored_task, 
                                               thread_to_task, task_to_thread, 
                                               exec_state, thread_is_new, 
                                               preemption_done, task_w, pid_, 
                                               head_, pid_s, head, pid_g, 
                                               pid_t, pid_se, ctx_, pid_p, 
                                               ctx_p, pid_w, task_, pid_ta, 
                                               thread, pid_m, thread_, pid_r, 
                                               pid_th, ctx, pid_set, next_ctx_, 
                                               pid_y, next_ctx, current_ctx_, 
                                               pid_yi, task_y, next_thread, 
                                               current_ctx, pid_ru, task_r, 
                                               pid_f, task_f, pid_pr, pid, 
                                               current_task, next_task, 
                                               next_thread_, task >>

continue_run_main2(self) == /\ pc[self] = "continue_run_main2"
                            /\ lock_info' = [lock_info EXCEPT ![task_r[self]] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
                            /\ UNCHANGED << queue, lock_future, lock_scheduler, 
                                            lock_THREADS, lock_THREAD_POOL, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, state, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREADS_running, 
                                            THREAD_POOL, PREEMPTED_TASKS, 
                                            NEXT_TASK, thread_index, 
                                            stored_ctx, stored_task, 
                                            thread_to_task, task_to_thread, 
                                            exec_state, thread_is_new, 
                                            preemption_done, stack, task_w, 
                                            task_wa, pid_, head_, pid_s, head, 
                                            pid_g, pid_t, pid_se, ctx_, pid_p, 
                                            ctx_p, pid_w, task_, pid_ta, 
                                            thread, pid_m, thread_, pid_r, 
                                            pid_th, ctx, pid_set, next_ctx_, 
                                            pid_y, next_ctx, current_ctx_, 
                                            pid_yi, task_y, next_thread, 
                                            current_ctx, pid_ru, task_r, pid_f, 
                                            task_f, pid_pr, pid, current_task, 
                                            next_task, next_thread_, task >>

run_main(self) == start_run_main(self) \/ get_next_run_main(self)
                     \/ get_task_run_main(self) \/ lock_task_run_main(self)
                     \/ yield_run_main(self) \/ continue_run_main(self)
                     \/ unlock_task_run_main(self)
                     \/ lock_future_run_main(self) \/ check_run_main(self)
                     \/ terminated_run_main(self)
                     \/ pre_future_run_main(self)
                     \/ set_task_run_main(self) \/ preempt_run_main(self)
                     \/ continue_run_main3(self)
                     \/ start_future_run_main(self)
                     \/ end_future_run_main(self)
                     \/ unset_task_run_main(self)
                     \/ post_future_run_main(self)
                     \/ sched_future_run_main(self)
                     \/ continue_run_main2(self)

start_future(self) == /\ pc[self] = "start_future"
                      /\ result_future' = [result_future EXCEPT ![pid_f[self]] = "Ready"]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ pid_f' = [pid_f EXCEPT ![self] = Head(stack[self]).pid_f]
                      /\ task_f' = [task_f EXCEPT ![self] = Head(stack[self]).task_f]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << queue, lock_info, lock_future, 
                                      lock_scheduler, lock_THREADS, 
                                      lock_THREAD_POOL, lock_PREEMPTED_TASKS, 
                                      lock_NEXT_TASK, lock_result_context, 
                                      in_queue, need_sched, state, result_next, 
                                      result_context, result_thread, RUNNING, 
                                      THREADS_pooled, THREADS_running, 
                                      THREAD_POOL, PREEMPTED_TASKS, NEXT_TASK, 
                                      thread_index, stored_ctx, stored_task, 
                                      thread_to_task, task_to_thread, 
                                      exec_state, thread_is_new, 
                                      preemption_done, task_w, task_wa, pid_, 
                                      head_, pid_s, head, pid_g, pid_t, pid_se, 
                                      ctx_, pid_p, ctx_p, pid_w, task_, pid_ta, 
                                      thread, pid_m, thread_, pid_r, pid_th, 
                                      ctx, pid_set, next_ctx_, pid_y, next_ctx, 
                                      current_ctx_, pid_yi, task_y, 
                                      next_thread, current_ctx, pid_ru, task_r, 
                                      pid_pr, pid, current_task, next_task, 
                                      next_thread_, task >>

future(self) == start_future(self)

start_preempt_init(self) == /\ pc[self] = "start_preempt_init"
                            /\ thread_index' = thread_index + 1
                            /\ /\ ctx_' = [ctx_ EXCEPT ![self] = thread_index']
                               /\ pid_se' = [pid_se EXCEPT ![self] = pid_pr[self]]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set_current_context",
                                                                        pc        |->  "end_preempt_init",
                                                                        pid_se    |->  pid_se[self],
                                                                        ctx_      |->  ctx_[self] ] >>
                                                                    \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "wait_set_current_context"]
                            /\ UNCHANGED << queue, lock_info, lock_future, 
                                            lock_scheduler, lock_THREADS, 
                                            lock_THREAD_POOL, 
                                            lock_PREEMPTED_TASKS, 
                                            lock_NEXT_TASK, 
                                            lock_result_context, in_queue, 
                                            need_sched, state, result_next, 
                                            result_future, result_context, 
                                            result_thread, RUNNING, 
                                            THREADS_pooled, THREADS_running, 
                                            THREAD_POOL, PREEMPTED_TASKS, 
                                            NEXT_TASK, stored_ctx, stored_task, 
                                            thread_to_task, task_to_thread, 
                                            exec_state, thread_is_new, 
                                            preemption_done, task_w, task_wa, 
                                            pid_, head_, pid_s, head, pid_g, 
                                            pid_t, pid_p, ctx_p, pid_w, task_, 
                                            pid_ta, thread, pid_m, thread_, 
                                            pid_r, pid_th, ctx, pid_set, 
                                            next_ctx_, pid_y, next_ctx, 
                                            current_ctx_, pid_yi, task_y, 
                                            next_thread, current_ctx, pid_ru, 
                                            task_r, pid_f, task_f, pid_pr, pid, 
                                            current_task, next_task, 
                                            next_thread_, task >>

end_preempt_init(self) == /\ pc[self] = "end_preempt_init"
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ pid_pr' = [pid_pr EXCEPT ![self] = Head(stack[self]).pid_pr]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << queue, lock_info, lock_future, 
                                          lock_scheduler, lock_THREADS, 
                                          lock_THREAD_POOL, 
                                          lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                                          lock_result_context, in_queue, 
                                          need_sched, state, result_next, 
                                          result_future, result_context, 
                                          result_thread, RUNNING, 
                                          THREADS_pooled, THREADS_running, 
                                          THREAD_POOL, PREEMPTED_TASKS, 
                                          NEXT_TASK, thread_index, stored_ctx, 
                                          stored_task, thread_to_task, 
                                          task_to_thread, exec_state, 
                                          thread_is_new, preemption_done, 
                                          task_w, task_wa, pid_, head_, pid_s, 
                                          head, pid_g, pid_t, pid_se, ctx_, 
                                          pid_p, ctx_p, pid_w, task_, pid_ta, 
                                          thread, pid_m, thread_, pid_r, 
                                          pid_th, ctx, pid_set, next_ctx_, 
                                          pid_y, next_ctx, current_ctx_, 
                                          pid_yi, task_y, next_thread, 
                                          current_ctx, pid_ru, task_r, pid_f, 
                                          task_f, pid, current_task, next_task, 
                                          next_thread_, task >>

preempt_init(self) == start_preempt_init(self) \/ end_preempt_init(self)

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
                                             lock_scheduler, lock_THREADS, 
                                             lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, thread_is_new, 
                                             preemption_done, stack, task_w, 
                                             task_wa, pid_, head_, pid_s, head, 
                                             pid_g, pid_t, pid_se, ctx_, pid_p, 
                                             ctx_p, pid_w, task_, pid_ta, 
                                             thread, pid_m, thread_, pid_r, 
                                             pid_th, ctx, pid_set, next_ctx_, 
                                             pid_y, next_ctx, current_ctx_, 
                                             pid_yi, task_y, next_thread, 
                                             current_ctx, pid_ru, task_r, 
                                             pid_f, task_f, pid_pr, pid, 
                                             next_task, task >>

get_current_task_do_preemption(self) == /\ pc[self] = "get_current_task_do_preemption"
                                        /\ current_task' = [current_task EXCEPT ![self] = RUNNING[pid[self]]]
                                        /\ IF RUNNING[pid[self]] < 0
                                              THEN /\ pc' = [pc EXCEPT ![self] = "exit_do_preemption1"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "get_next_task_do_preemption"]
                                        /\ UNCHANGED << queue, lock_info, 
                                                        lock_future, 
                                                        lock_scheduler, 
                                                        lock_THREADS, 
                                                        lock_THREAD_POOL, 
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
                                                        stored_ctx, 
                                                        stored_task, 
                                                        thread_to_task, 
                                                        task_to_thread, 
                                                        exec_state, 
                                                        thread_is_new, 
                                                        preemption_done, stack, 
                                                        task_w, task_wa, pid_, 
                                                        head_, pid_s, head, 
                                                        pid_g, pid_t, pid_se, 
                                                        ctx_, pid_p, ctx_p, 
                                                        pid_w, task_, pid_ta, 
                                                        thread, pid_m, thread_, 
                                                        pid_r, pid_th, ctx, 
                                                        pid_set, next_ctx_, 
                                                        pid_y, next_ctx, 
                                                        current_ctx_, pid_yi, 
                                                        task_y, next_thread, 
                                                        current_ctx, pid_ru, 
                                                        task_r, pid_f, task_f, 
                                                        pid_pr, pid, next_task, 
                                                        next_thread_, task >>

exit_do_preemption1(self) == /\ pc[self] = "exit_do_preemption1"
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ current_task' = [current_task EXCEPT ![self] = Head(stack[self]).current_task]
                             /\ next_task' = [next_task EXCEPT ![self] = Head(stack[self]).next_task]
                             /\ next_thread_' = [next_thread_ EXCEPT ![self] = Head(stack[self]).next_thread_]
                             /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << queue, lock_info, lock_future, 
                                             lock_scheduler, lock_THREADS, 
                                             lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, thread_is_new, 
                                             preemption_done, task_w, task_wa, 
                                             pid_, head_, pid_s, head, pid_g, 
                                             pid_t, pid_se, ctx_, pid_p, ctx_p, 
                                             pid_w, task_, pid_ta, thread, 
                                             pid_m, thread_, pid_r, pid_th, 
                                             ctx, pid_set, next_ctx_, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, pid_f, task_f, 
                                             pid_pr, task >>

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
                                                     lock_THREADS, 
                                                     lock_THREAD_POOL, 
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
                                                     stored_ctx, stored_task, 
                                                     thread_to_task, 
                                                     task_to_thread, 
                                                     exec_state, thread_is_new, 
                                                     preemption_done, task_w, 
                                                     task_wa, pid_, head_, 
                                                     pid_s, head, pid_t, 
                                                     pid_se, ctx_, pid_p, 
                                                     ctx_p, pid_w, task_, 
                                                     pid_ta, thread, pid_m, 
                                                     thread_, pid_r, pid_th, 
                                                     ctx, pid_set, next_ctx_, 
                                                     pid_y, next_ctx, 
                                                     current_ctx_, pid_yi, 
                                                     task_y, next_thread, 
                                                     current_ctx, pid_ru, 
                                                     task_r, pid_f, task_f, 
                                                     pid_pr, pid, current_task, 
                                                     next_task, next_thread_, 
                                                     task >>

set_task_do_preemption(self) == /\ pc[self] = "set_task_do_preemption"
                                /\ next_task' = [next_task EXCEPT ![self] = result_next[pid[self]]]
                                /\ IF next_task'[self] < 0
                                      THEN /\ pc' = [pc EXCEPT ![self] = "exit_do_preemption2"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "lock_task_do_preemption"]
                                /\ UNCHANGED << queue, lock_info, lock_future, 
                                                lock_scheduler, lock_THREADS, 
                                                lock_THREAD_POOL, 
                                                lock_PREEMPTED_TASKS, 
                                                lock_NEXT_TASK, 
                                                lock_result_context, in_queue, 
                                                need_sched, state, result_next, 
                                                result_future, result_context, 
                                                result_thread, RUNNING, 
                                                THREADS_pooled, 
                                                THREADS_running, THREAD_POOL, 
                                                PREEMPTED_TASKS, NEXT_TASK, 
                                                thread_index, stored_ctx, 
                                                stored_task, thread_to_task, 
                                                task_to_thread, exec_state, 
                                                thread_is_new, preemption_done, 
                                                stack, task_w, task_wa, pid_, 
                                                head_, pid_s, head, pid_g, 
                                                pid_t, pid_se, ctx_, pid_p, 
                                                ctx_p, pid_w, task_, pid_ta, 
                                                thread, pid_m, thread_, pid_r, 
                                                pid_th, ctx, pid_set, 
                                                next_ctx_, pid_y, next_ctx, 
                                                current_ctx_, pid_yi, task_y, 
                                                next_thread, current_ctx, 
                                                pid_ru, task_r, pid_f, task_f, 
                                                pid_pr, pid, current_task, 
                                                next_thread_, task >>

exit_do_preemption2(self) == /\ pc[self] = "exit_do_preemption2"
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ current_task' = [current_task EXCEPT ![self] = Head(stack[self]).current_task]
                             /\ next_task' = [next_task EXCEPT ![self] = Head(stack[self]).next_task]
                             /\ next_thread_' = [next_thread_ EXCEPT ![self] = Head(stack[self]).next_thread_]
                             /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << queue, lock_info, lock_future, 
                                             lock_scheduler, lock_THREADS, 
                                             lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, thread_is_new, 
                                             preemption_done, task_w, task_wa, 
                                             pid_, head_, pid_s, head, pid_g, 
                                             pid_t, pid_se, ctx_, pid_p, ctx_p, 
                                             pid_w, task_, pid_ta, thread, 
                                             pid_m, thread_, pid_r, pid_th, 
                                             ctx, pid_set, next_ctx_, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, pid_f, task_f, 
                                             pid_pr, task >>

lock_task_do_preemption(self) == /\ pc[self] = "lock_task_do_preemption"
                                 /\ ~lock_info[next_task[self]]
                                 /\ lock_info' = [lock_info EXCEPT ![next_task[self]] = TRUE]
                                 /\ next_thread_' = [next_thread_ EXCEPT ![self] = task_to_thread[next_task[self]]]
                                 /\ pc' = [pc EXCEPT ![self] = "yield_do_preemption"]
                                 /\ UNCHANGED << queue, lock_future, 
                                                 lock_scheduler, lock_THREADS, 
                                                 lock_THREAD_POOL, 
                                                 lock_PREEMPTED_TASKS, 
                                                 lock_NEXT_TASK, 
                                                 lock_result_context, in_queue, 
                                                 need_sched, state, 
                                                 result_next, result_future, 
                                                 result_context, result_thread, 
                                                 RUNNING, THREADS_pooled, 
                                                 THREADS_running, THREAD_POOL, 
                                                 PREEMPTED_TASKS, NEXT_TASK, 
                                                 thread_index, stored_ctx, 
                                                 stored_task, thread_to_task, 
                                                 task_to_thread, exec_state, 
                                                 thread_is_new, 
                                                 preemption_done, stack, 
                                                 task_w, task_wa, pid_, head_, 
                                                 pid_s, head, pid_g, pid_t, 
                                                 pid_se, ctx_, pid_p, ctx_p, 
                                                 pid_w, task_, pid_ta, thread, 
                                                 pid_m, thread_, pid_r, pid_th, 
                                                 ctx, pid_set, next_ctx_, 
                                                 pid_y, next_ctx, current_ctx_, 
                                                 pid_yi, task_y, next_thread, 
                                                 current_ctx, pid_ru, task_r, 
                                                 pid_f, task_f, pid_pr, pid, 
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
                                             lock_scheduler, lock_THREADS, 
                                             lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, thread_is_new, 
                                             preemption_done, task_w, task_wa, 
                                             pid_, head_, pid_s, head, pid_g, 
                                             pid_t, pid_se, ctx_, pid_p, ctx_p, 
                                             pid_w, task_, pid_ta, thread, 
                                             pid_m, thread_, pid_r, pid_th, 
                                             ctx, pid_set, next_ctx_, pid_y, 
                                             next_ctx, current_ctx_, pid_ru, 
                                             task_r, pid_f, task_f, pid_pr, 
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
                                             lock_scheduler, lock_THREADS, 
                                             lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, thread_is_new, 
                                             preemption_done, task_w, task_wa, 
                                             pid_, head_, pid_s, head, pid_g, 
                                             pid_t, pid_se, ctx_, pid_p, ctx_p, 
                                             pid_w, task_, pid_ta, thread, 
                                             pid_m, thread_, pid_r, pid_th, 
                                             ctx, pid_set, next_ctx_, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, pid_f, task_f, 
                                             pid_pr, task >>

unlock_task_do_preemption(self) == /\ pc[self] = "unlock_task_do_preemption"
                                   /\ lock_info' = [lock_info EXCEPT ![next_task[self]] = FALSE]
                                   /\ pc' = [pc EXCEPT ![self] = "take_thread_do_preemption"]
                                   /\ UNCHANGED << queue, lock_future, 
                                                   lock_scheduler, 
                                                   lock_THREADS, 
                                                   lock_THREAD_POOL, 
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
                                                   PREEMPTED_TASKS, NEXT_TASK, 
                                                   thread_index, stored_ctx, 
                                                   stored_task, thread_to_task, 
                                                   task_to_thread, exec_state, 
                                                   thread_is_new, 
                                                   preemption_done, stack, 
                                                   task_w, task_wa, pid_, 
                                                   head_, pid_s, head, pid_g, 
                                                   pid_t, pid_se, ctx_, pid_p, 
                                                   ctx_p, pid_w, task_, pid_ta, 
                                                   thread, pid_m, thread_, 
                                                   pid_r, pid_th, ctx, pid_set, 
                                                   next_ctx_, pid_y, next_ctx, 
                                                   current_ctx_, pid_yi, 
                                                   task_y, next_thread, 
                                                   current_ctx, pid_ru, task_r, 
                                                   pid_f, task_f, pid_pr, pid, 
                                                   current_task, next_task, 
                                                   next_thread_, task >>

take_thread_do_preemption(self) == /\ pc[self] = "take_thread_do_preemption"
                                   /\ /\ pid_ta' = [pid_ta EXCEPT ![self] = pid[self]]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "take_pooled_thread",
                                                                               pc        |->  "create_thread_do_preemption",
                                                                               pid_ta    |->  pid_ta[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "start_take_pooled_thread"]
                                   /\ UNCHANGED << queue, lock_info, 
                                                   lock_future, lock_scheduler, 
                                                   lock_THREADS, 
                                                   lock_THREAD_POOL, 
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
                                                   PREEMPTED_TASKS, NEXT_TASK, 
                                                   thread_index, stored_ctx, 
                                                   stored_task, thread_to_task, 
                                                   task_to_thread, exec_state, 
                                                   thread_is_new, 
                                                   preemption_done, task_w, 
                                                   task_wa, pid_, head_, pid_s, 
                                                   head, pid_g, pid_t, pid_se, 
                                                   ctx_, pid_p, ctx_p, pid_w, 
                                                   task_, thread, pid_m, 
                                                   thread_, pid_r, pid_th, ctx, 
                                                   pid_set, next_ctx_, pid_y, 
                                                   next_ctx, current_ctx_, 
                                                   pid_yi, task_y, next_thread, 
                                                   current_ctx, pid_ru, task_r, 
                                                   pid_f, task_f, pid_pr, pid, 
                                                   current_task, next_task, 
                                                   next_thread_, task >>

create_thread_do_preemption(self) == /\ pc[self] = "create_thread_do_preemption"
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
                                                     lock_future, 
                                                     lock_scheduler, 
                                                     lock_THREADS, 
                                                     lock_THREAD_POOL, 
                                                     lock_PREEMPTED_TASKS, 
                                                     lock_NEXT_TASK, 
                                                     lock_result_context, 
                                                     in_queue, need_sched, 
                                                     state, result_next, 
                                                     result_future, 
                                                     result_context, RUNNING, 
                                                     THREADS_pooled, 
                                                     THREADS_running, 
                                                     THREAD_POOL, 
                                                     PREEMPTED_TASKS, 
                                                     NEXT_TASK, stored_ctx, 
                                                     stored_task, 
                                                     thread_to_task, 
                                                     task_to_thread, 
                                                     exec_state, 
                                                     preemption_done, stack, 
                                                     task_w, task_wa, pid_, 
                                                     head_, pid_s, head, pid_g, 
                                                     pid_t, pid_se, ctx_, 
                                                     pid_p, ctx_p, pid_w, 
                                                     task_, pid_ta, thread, 
                                                     pid_m, thread_, pid_r, 
                                                     pid_th, ctx, pid_set, 
                                                     next_ctx_, pid_y, 
                                                     next_ctx, current_ctx_, 
                                                     pid_yi, task_y, 
                                                     next_thread, current_ctx, 
                                                     pid_ru, task_r, pid_f, 
                                                     task_f, pid_pr, pid, 
                                                     current_task, next_task, 
                                                     next_thread_, task >>

set_thread_do_preemption(self) == /\ pc[self] = "set_thread_do_preemption"
                                  /\ next_thread_' = [next_thread_ EXCEPT ![self] = result_thread[pid[self]]]
                                  /\ pc' = [pc EXCEPT ![self] = "wait_NEXT_TASK_do_preemption"]
                                  /\ UNCHANGED << queue, lock_info, 
                                                  lock_future, lock_scheduler, 
                                                  lock_THREADS, 
                                                  lock_THREAD_POOL, 
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
                                                  thread_index, stored_ctx, 
                                                  stored_task, thread_to_task, 
                                                  task_to_thread, exec_state, 
                                                  thread_is_new, 
                                                  preemption_done, stack, 
                                                  task_w, task_wa, pid_, head_, 
                                                  pid_s, head, pid_g, pid_t, 
                                                  pid_se, ctx_, pid_p, ctx_p, 
                                                  pid_w, task_, pid_ta, thread, 
                                                  pid_m, thread_, pid_r, 
                                                  pid_th, ctx, pid_set, 
                                                  next_ctx_, pid_y, next_ctx, 
                                                  current_ctx_, pid_yi, task_y, 
                                                  next_thread, current_ctx, 
                                                  pid_ru, task_r, pid_f, 
                                                  task_f, pid_pr, pid, 
                                                  current_task, next_task, 
                                                  task >>

wait_NEXT_TASK_do_preemption(self) == /\ pc[self] = "wait_NEXT_TASK_do_preemption"
                                      /\ ~lock_NEXT_TASK[pid[self]]
                                      /\ lock_NEXT_TASK' = [lock_NEXT_TASK EXCEPT ![pid[self]] = TRUE]
                                      /\ pc' = [pc EXCEPT ![self] = "push_NEXT_TASK_do_preemption"]
                                      /\ UNCHANGED << queue, lock_info, 
                                                      lock_future, 
                                                      lock_scheduler, 
                                                      lock_THREADS, 
                                                      lock_THREAD_POOL, 
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
                                                      stored_ctx, stored_task, 
                                                      thread_to_task, 
                                                      task_to_thread, 
                                                      exec_state, 
                                                      thread_is_new, 
                                                      preemption_done, stack, 
                                                      task_w, task_wa, pid_, 
                                                      head_, pid_s, head, 
                                                      pid_g, pid_t, pid_se, 
                                                      ctx_, pid_p, ctx_p, 
                                                      pid_w, task_, pid_ta, 
                                                      thread, pid_m, thread_, 
                                                      pid_r, pid_th, ctx, 
                                                      pid_set, next_ctx_, 
                                                      pid_y, next_ctx, 
                                                      current_ctx_, pid_yi, 
                                                      task_y, next_thread, 
                                                      current_ctx, pid_ru, 
                                                      task_r, pid_f, task_f, 
                                                      pid_pr, pid, 
                                                      current_task, next_task, 
                                                      next_thread_, task >>

push_NEXT_TASK_do_preemption(self) == /\ pc[self] = "push_NEXT_TASK_do_preemption"
                                      /\ NEXT_TASK' = [NEXT_TASK EXCEPT ![pid[self]] = Append(NEXT_TASK[pid[self]], next_task[self])]
                                      /\ lock_NEXT_TASK' = [lock_NEXT_TASK EXCEPT ![pid[self]] = FALSE]
                                      /\ pc' = [pc EXCEPT ![self] = "end_do_preemption"]
                                      /\ UNCHANGED << queue, lock_info, 
                                                      lock_future, 
                                                      lock_scheduler, 
                                                      lock_THREADS, 
                                                      lock_THREAD_POOL, 
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
                                                      thread_index, stored_ctx, 
                                                      stored_task, 
                                                      thread_to_task, 
                                                      task_to_thread, 
                                                      exec_state, 
                                                      thread_is_new, 
                                                      preemption_done, stack, 
                                                      task_w, task_wa, pid_, 
                                                      head_, pid_s, head, 
                                                      pid_g, pid_t, pid_se, 
                                                      ctx_, pid_p, ctx_p, 
                                                      pid_w, task_, pid_ta, 
                                                      thread, pid_m, thread_, 
                                                      pid_r, pid_th, ctx, 
                                                      pid_set, next_ctx_, 
                                                      pid_y, next_ctx, 
                                                      current_ctx_, pid_yi, 
                                                      task_y, next_thread, 
                                                      current_ctx, pid_ru, 
                                                      task_r, pid_f, task_f, 
                                                      pid_pr, pid, 
                                                      current_task, next_task, 
                                                      next_thread_, task >>

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
                                           lock_scheduler, lock_THREADS, 
                                           lock_THREAD_POOL, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, stored_ctx, 
                                           stored_task, thread_to_task, 
                                           task_to_thread, exec_state, 
                                           thread_is_new, preemption_done, 
                                           task_w, task_wa, pid_, head_, pid_s, 
                                           head, pid_g, pid_t, pid_se, ctx_, 
                                           pid_p, ctx_p, pid_w, task_, pid_ta, 
                                           thread, pid_m, thread_, pid_r, 
                                           pid_th, ctx, pid_set, next_ctx_, 
                                           pid_y, next_ctx, current_ctx_, 
                                           pid_ru, task_r, pid_f, task_f, 
                                           pid_pr, pid, current_task, 
                                           next_task, next_thread_, task >>

exit_do_preemption4(self) == /\ pc[self] = "exit_do_preemption4"
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ current_task' = [current_task EXCEPT ![self] = Head(stack[self]).current_task]
                             /\ next_task' = [next_task EXCEPT ![self] = Head(stack[self]).next_task]
                             /\ next_thread_' = [next_thread_ EXCEPT ![self] = Head(stack[self]).next_thread_]
                             /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << queue, lock_info, lock_future, 
                                             lock_scheduler, lock_THREADS, 
                                             lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, thread_is_new, 
                                             preemption_done, task_w, task_wa, 
                                             pid_, head_, pid_s, head, pid_g, 
                                             pid_t, pid_se, ctx_, pid_p, ctx_p, 
                                             pid_w, task_, pid_ta, thread, 
                                             pid_m, thread_, pid_r, pid_th, 
                                             ctx, pid_set, next_ctx_, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, pid_f, task_f, 
                                             pid_pr, task >>

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
                          \/ take_thread_do_preemption(self)
                          \/ create_thread_do_preemption(self)
                          \/ set_thread_do_preemption(self)
                          \/ wait_NEXT_TASK_do_preemption(self)
                          \/ push_NEXT_TASK_do_preemption(self)
                          \/ end_do_preemption(self)
                          \/ exit_do_preemption4(self)

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
                                             lock_scheduler, lock_THREADS, 
                                             lock_THREAD_POOL, 
                                             lock_PREEMPTED_TASKS, 
                                             lock_NEXT_TASK, 
                                             lock_result_context, in_queue, 
                                             need_sched, state, result_next, 
                                             result_future, result_context, 
                                             result_thread, RUNNING, 
                                             THREADS_pooled, THREADS_running, 
                                             THREAD_POOL, PREEMPTED_TASKS, 
                                             NEXT_TASK, thread_index, 
                                             stored_ctx, stored_task, 
                                             thread_to_task, task_to_thread, 
                                             exec_state, thread_is_new, 
                                             preemption_done, task_w, pid_, 
                                             head_, pid_s, head, pid_g, pid_t, 
                                             pid_se, ctx_, pid_p, ctx_p, pid_w, 
                                             task_, pid_ta, thread, pid_m, 
                                             thread_, pid_r, pid_th, ctx, 
                                             pid_set, next_ctx_, pid_y, 
                                             next_ctx, current_ctx_, pid_yi, 
                                             task_y, next_thread, current_ctx, 
                                             pid_ru, task_r, pid_f, task_f, 
                                             pid_pr, pid, current_task, 
                                             next_task, next_thread_ >>

rec_wake_task_all(self) == /\ pc[self] = "rec_wake_task_all"
                           /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_task_all",
                                                                       pc        |->  "end_wake_task_all",
                                                                       task      |->  task[self] ] >>
                                                                   \o stack[self]]
                              /\ task' = [task EXCEPT ![self] = task[self] + 1]
                           /\ pc' = [pc EXCEPT ![self] = "start_wake_task_all"]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, lock_THREADS, 
                                           lock_THREAD_POOL, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, stored_ctx, 
                                           stored_task, thread_to_task, 
                                           task_to_thread, exec_state, 
                                           thread_is_new, preemption_done, 
                                           task_w, task_wa, pid_, head_, pid_s, 
                                           head, pid_g, pid_t, pid_se, ctx_, 
                                           pid_p, ctx_p, pid_w, task_, pid_ta, 
                                           thread, pid_m, thread_, pid_r, 
                                           pid_th, ctx, pid_set, next_ctx_, 
                                           pid_y, next_ctx, current_ctx_, 
                                           pid_yi, task_y, next_thread, 
                                           current_ctx, pid_ru, task_r, pid_f, 
                                           task_f, pid_pr, pid, current_task, 
                                           next_task, next_thread_ >>

end_wake_task_all(self) == /\ pc[self] = "end_wake_task_all"
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ task' = [task EXCEPT ![self] = Head(stack[self]).task]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << queue, lock_info, lock_future, 
                                           lock_scheduler, lock_THREADS, 
                                           lock_THREAD_POOL, 
                                           lock_PREEMPTED_TASKS, 
                                           lock_NEXT_TASK, lock_result_context, 
                                           in_queue, need_sched, state, 
                                           result_next, result_future, 
                                           result_context, result_thread, 
                                           RUNNING, THREADS_pooled, 
                                           THREADS_running, THREAD_POOL, 
                                           PREEMPTED_TASKS, NEXT_TASK, 
                                           thread_index, stored_ctx, 
                                           stored_task, thread_to_task, 
                                           task_to_thread, exec_state, 
                                           thread_is_new, preemption_done, 
                                           task_w, task_wa, pid_, head_, pid_s, 
                                           head, pid_g, pid_t, pid_se, ctx_, 
                                           pid_p, ctx_p, pid_w, task_, pid_ta, 
                                           thread, pid_m, thread_, pid_r, 
                                           pid_th, ctx, pid_set, next_ctx_, 
                                           pid_y, next_ctx, current_ctx_, 
                                           pid_yi, task_y, next_thread, 
                                           current_ctx, pid_ru, task_r, pid_f, 
                                           task_f, pid_pr, pid, current_task, 
                                           next_task, next_thread_ >>

wake_task_all(self) == start_wake_task_all(self) \/ rec_wake_task_all(self)
                          \/ end_wake_task_all(self)

start_worker(self) == /\ pc[self] = "start_worker"
                      /\ IF self = 1
                            THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wake_task_all",
                                                                             pc        |->  "preempt_init_",
                                                                             task      |->  task[self] ] >>
                                                                         \o stack[self]]
                                    /\ task' = [task EXCEPT ![self] = self]
                                 /\ pc' = [pc EXCEPT ![self] = "start_wake_task_all"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "preempt_init_"]
                                 /\ UNCHANGED << stack, task >>
                      /\ UNCHANGED << queue, lock_info, lock_future, 
                                      lock_scheduler, lock_THREADS, 
                                      lock_THREAD_POOL, lock_PREEMPTED_TASKS, 
                                      lock_NEXT_TASK, lock_result_context, 
                                      in_queue, need_sched, state, result_next, 
                                      result_future, result_context, 
                                      result_thread, RUNNING, THREADS_pooled, 
                                      THREADS_running, THREAD_POOL, 
                                      PREEMPTED_TASKS, NEXT_TASK, thread_index, 
                                      stored_ctx, stored_task, thread_to_task, 
                                      task_to_thread, exec_state, 
                                      thread_is_new, preemption_done, task_w, 
                                      task_wa, pid_, head_, pid_s, head, pid_g, 
                                      pid_t, pid_se, ctx_, pid_p, ctx_p, pid_w, 
                                      task_, pid_ta, thread, pid_m, thread_, 
                                      pid_r, pid_th, ctx, pid_set, next_ctx_, 
                                      pid_y, next_ctx, current_ctx_, pid_yi, 
                                      task_y, next_thread, current_ctx, pid_ru, 
                                      task_r, pid_f, task_f, pid_pr, pid, 
                                      current_task, next_task, next_thread_ >>

preempt_init_(self) == /\ pc[self] = "preempt_init_"
                       /\ /\ pid_pr' = [pid_pr EXCEPT ![self] = self]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "preempt_init",
                                                                   pc        |->  "run",
                                                                   pid_pr    |->  pid_pr[self] ] >>
                                                               \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "start_preempt_init"]
                       /\ UNCHANGED << queue, lock_info, lock_future, 
                                       lock_scheduler, lock_THREADS, 
                                       lock_THREAD_POOL, lock_PREEMPTED_TASKS, 
                                       lock_NEXT_TASK, lock_result_context, 
                                       in_queue, need_sched, state, 
                                       result_next, result_future, 
                                       result_context, result_thread, RUNNING, 
                                       THREADS_pooled, THREADS_running, 
                                       THREAD_POOL, PREEMPTED_TASKS, NEXT_TASK, 
                                       thread_index, stored_ctx, stored_task, 
                                       thread_to_task, task_to_thread, 
                                       exec_state, thread_is_new, 
                                       preemption_done, task_w, task_wa, pid_, 
                                       head_, pid_s, head, pid_g, pid_t, 
                                       pid_se, ctx_, pid_p, ctx_p, pid_w, 
                                       task_, pid_ta, thread, pid_m, thread_, 
                                       pid_r, pid_th, ctx, pid_set, next_ctx_, 
                                       pid_y, next_ctx, current_ctx_, pid_yi, 
                                       task_y, next_thread, current_ctx, 
                                       pid_ru, task_r, pid_f, task_f, pid, 
                                       current_task, next_task, next_thread_, 
                                       task >>

run(self) == /\ pc[self] = "run"
             /\ /\ pid_ru' = [pid_ru EXCEPT ![self] = self]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "run_main",
                                                         pc        |->  "Done",
                                                         task_r    |->  task_r[self],
                                                         pid_ru    |->  pid_ru[self] ] >>
                                                     \o stack[self]]
             /\ task_r' = [task_r EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "start_run_main"]
             /\ UNCHANGED << queue, lock_info, lock_future, lock_scheduler, 
                             lock_THREADS, lock_THREAD_POOL, 
                             lock_PREEMPTED_TASKS, lock_NEXT_TASK, 
                             lock_result_context, in_queue, need_sched, state, 
                             result_next, result_future, result_context, 
                             result_thread, RUNNING, THREADS_pooled, 
                             THREADS_running, THREAD_POOL, PREEMPTED_TASKS, 
                             NEXT_TASK, thread_index, stored_ctx, stored_task, 
                             thread_to_task, task_to_thread, exec_state, 
                             thread_is_new, preemption_done, task_w, task_wa, 
                             pid_, head_, pid_s, head, pid_g, pid_t, pid_se, 
                             ctx_, pid_p, ctx_p, pid_w, task_, pid_ta, thread, 
                             pid_m, thread_, pid_r, pid_th, ctx, pid_set, 
                             next_ctx_, pid_y, next_ctx, current_ctx_, pid_yi, 
                             task_y, next_thread, current_ctx, pid_f, task_f, 
                             pid_pr, pid, current_task, next_task, 
                             next_thread_, task >>

W(self) == start_worker(self) \/ preempt_init_(self) \/ run(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ wake_task(self) \/ wake(self)
                               \/ preempt_get_next_task(self)
                               \/ scheduler_get_next(self)
                               \/ get_next_task(self)
                               \/ take_current_context(self)
                               \/ set_current_context(self)
                               \/ push_to_thread_pool(self)
                               \/ wake_PREEMPTED_TASKS(self)
                               \/ take_pooled_thread(self)
                               \/ make_thread_pooled(self)
                               \/ make_all_threads_pooled(self)
                               \/ re_schedule(self) \/ thread_entry(self)
                               \/ set_exec_state(self)
                               \/ yield_and_pool(self)
                               \/ yield_preempted_and_wake_task(self)
                               \/ run_main(self) \/ future(self)
                               \/ preempt_init(self) \/ do_preemption(self)
                               \/ wake_task_all(self))
           \/ (\E self \in WORKERS: W(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in WORKERS : /\ SF_vars(W(self))
                                 /\ SF_vars(wake_task_all(self))
                                 /\ SF_vars(preempt_init(self))
                                 /\ SF_vars(run_main(self))
                                 /\ SF_vars(wake_task(self))
                                 /\ SF_vars(wake(self))
                                 /\ SF_vars(set_current_context(self))
                                 /\ SF_vars(preempt_get_next_task(self))
                                 /\ SF_vars(scheduler_get_next(self))
                                 /\ SF_vars(get_next_task(self))
                                 /\ SF_vars(take_current_context(self))
                                 /\ SF_vars(push_to_thread_pool(self))
                                 /\ SF_vars(wake_PREEMPTED_TASKS(self))
                                 /\ SF_vars(take_pooled_thread(self))
                                 /\ SF_vars(make_thread_pooled(self))
                                 /\ SF_vars(make_all_threads_pooled(self))
                                 /\ SF_vars(re_schedule(self))
                                 /\ SF_vars(thread_entry(self))
                                 /\ SF_vars(set_exec_state(self))
                                 /\ SF_vars(yield_and_pool(self))
                                 /\ SF_vars(yield_preempted_and_wake_task(self))                                 /\ SF_vars(future(self))
                                 /\ SF_vars(do_preemption(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
