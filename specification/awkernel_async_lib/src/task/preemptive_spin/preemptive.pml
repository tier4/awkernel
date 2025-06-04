#define TASK_NUM 4
#define WORKER_NUM TASK_NUM// Prepare same number of worker threads as tasks.
#define CPU_NUM 2
#define NUM_PROC WORKER_NUM

#include "future_mock.pml"
#include "../cooperative_spin/fair_lock.pml"

FairLock lock_info[TASK_NUM];
FairLock lock_future[TASK_NUM];
FairLock lock_queue = false;
FairLock lock_next_task = false;

typedef Worker {
	short executing_in;// cpu_id when this is executed, -1 otherwise.
	bool used_as_preempt_ctx;
}

Worker workers[WORKER_NUM];

mtype = { Ready,Runnable,Running,Waiting,Terminated,Pending,Preempted };// Panic is not considered.

/* awkernel_async_lib::task::TaskInfo */
typedef TaskInfo {
	mtype state;
	bool need_sched;
	bool is_terminated;
	byte id;// This also represents the priority of the task. The lower the value, the higher the priority.
	bool need_preemption;
	int thread;// tid when this task is preempted, -1 otherwise.
};

TaskInfo tasks[TASK_NUM];

short RUNNING[CPU_NUM] = - 1;// task_id when this CPU is executing a task, -1 otherwise.
short NEXT_TASK[CPU_NUM] = - 1;// Preempted task_id to be executed next, -1 if there is no preempted task.

chan ipi_requests[CPU_NUM] = [CPU_NUM] of { byte };// Message type is not accessed.
bool interrupted[CPU_NUM] = false;// true if this CPU is interrupted by an IPI request, false otherwise.
bool interrupt_enabled[CPU_NUM] = false;

/* Queue of the PrioritizedFIFO scheduler */
chan queue = [TASK_NUM * 2] of { byte };// task_ids in ascending order of priority.

int num_terminated = 0;// For verification.

inline exists_idle_cpu(ret) {
	ret = false;
	byte j;
	for (j : 0 .. CPU_NUM - 1) {
		if
		:: RUNNING[j] == - 1 -> ret = true;break;
		:: else
		fi
	}
}

inline get_lowest_priority_task(ret_task,ret_cpu_id) {
	ret_task = - 1;
	byte j;
	for (j : 0 .. CPU_NUM - 1) {
		if
		:: RUNNING[j] != - 1 -> 
			if
			:: RUNNING[j] > ret_task -> 
				ret_task = RUNNING[j];
				ret_cpu_id = j;
			:: else
			fi
		:: else -> ret_task = -1;break;
		fi
	}

	// ret_task may be -1, if there is idle CPU.
}

inline set_need_preemption(tid,task) {
	lock(tid,lock_info[task]);
	tasks[task].need_preemption = true;
	unlock(tid,lock_info[task]);
}

inline invoke_preemption(tid,task) {
	bool exists_idle;
	exists_idle_cpu(exists_idle);
	if
	:: exists_idle -> goto finish_invoke_preemption;
	:: else
	fi
	
	int lp_task;
	int lp_cpu_id;
	get_lowest_priority_task(lp_task,lp_cpu_id);
	if
	:: task < lp_task -> // If lp_task is -1, preemption will not occur.
		set_need_preemption(tid,lp_task);
		printf("invoke_preemption() send IPI: hp_task = %d,lp_task = %d,lp_cpu_id = %d,interrupt_enabled[lp_cpu_id] = %d\n",task,lp_task,lp_cpu_id,interrupt_enabled[lp_cpu_id]);
		ipi_requests[lp_cpu_id]!task;
	:: else
	fi
	
	finish_invoke_preemption:
}

/* awkernel_async_lib::scheduler::fifo::PrioritizedFIFOScheduler::wake_task() */
inline wake_task(tid,task) {
	lock(tid,lock_queue);
	queue!!task;
	unlock(tid,lock_queue);
	
	invoke_preemption(tid,task);
}

/* awkernel_async_lib::task::ArcWake::wake() */
inline wake(tid,task) {
	lock(tid,lock_info[task]);
	
	if
	:: tasks[task].state == Running || tasks[task].state == Runnable || tasks[task].state == Preempted -> 
		tasks[task].need_sched = true;
		printf("wake() set need_sched: tid = %d,task = %d,state = %e\n",tid,task,tasks[task].state);
		unlock(tid,lock_info[task]);
	:: tasks[task].state == Terminated -> 
		printf("wake() already terminated: tid = %d,task = %d,state = %e\n",tid,task,tasks[task].state);
		unlock(tid,lock_info[task]);
	:: tasks[task].state == Waiting || tasks[task].state == Ready -> 
		printf("wake() call wake_task(): tid = %d,task = %d,state = %e\n",tid,task,tasks[task].state);
		tasks[task].state = Runnable;
		unlock(tid,lock_info[task]);
		wake_task(tid,task);
	fi
}

/* awkernel_async_lib::scheduler::fifo::FIFOScheduler::get_next_task() */
inline scheduler_get_next(tid,ret) {
	lock(tid,lock_queue);
	
	int head;
	
	start_get_next:
	
	if
	:: atomic { queue?[head] -> queue?head };
		lock(tid,lock_info[head]);
		
		if
		:: tasks[head].state == Terminated -> 
			unlock(tid,lock_info[head]);
			goto start_get_next;
		:: tasks[head].state == Preempted -> 
			tasks[head].need_preemption = false;
		:: else
		fi
		
		tasks[head].state = Running;
		printf("scheduler_get_next(): tid = %d,Chosen task = %d\n",tid,head);
		
		unlock(tid,lock_info[head]);
		unlock(tid,lock_queue);
		ret = head;
	:: else ->
		unlock(tid,lock_queue);
		ret = - 1;
	fi
}

/* awkernel_async_lib::task::preempt::get_next_task() */
inline preempt_get_next(tid,ret) {
	short cpu_id_ = workers[tid].executing_in;
	assert(cpu_id_ != - 1);

	ret = -1;
	lock(tid,lock_next_task);
	if
	:: NEXT_TASK[cpu_id_] != - 1 -> 
		ret = NEXT_TASK[cpu_id_];
		NEXT_TASK[cpu_id_] = - 1;
	:: else
	fi
	unlock(tid,lock_next_task);
}

/* awkernel_async_lib::task::get_next_task() */
inline get_next_task(tid,ret) {
	preempt_get_next(tid,ret);
	if
	:: ret == - 1 -> 
		scheduler_get_next(tid,ret);
	:: else
	fi
}

inline context_switch(cpu_id,cur_tid,next_tid) {
	printf("context_switch(): cpu_id = %d,cur_tid = %d,next_tid = %d\n",cpu_id,cur_tid,next_tid);
	assert(workers[cur_tid].executing_in == cpu_id);
	workers[next_tid].executing_in = cpu_id;
	workers[cur_tid].executing_in = - 1;
}

inline yield_preempted_and_wake_task(cpu_id,cur_task,cur_tid,next_tid) {
	lock(cur_tid,lock_info[cur_task]);
	tasks[cur_task].thread = cur_tid;
	tasks[cur_task].state = Preempted;
	unlock(cur_tid,lock_info[cur_task]);
	workers[cur_tid].used_as_preempt_ctx = true;
	context_switch(cpu_id,tasks[cur_task].thread,next_tid);
	wake_task(next_tid,cur_task);// re_schedule()
}

inline take_pooled_thread(ret) {
	ret = - 1;
	int k;
	for (k : 0 .. WORKER_NUM - 1) {
		if
		:: (workers[k].executing_in == - 1 && !workers[k].used_as_preempt_ctx) -> 
			ret = k;
			break;
		:: else
		fi
	}
	
	assert(ret != - 1);
}

inline take_preempt_context(task,ret) {
	ret = tasks[task].thread;
	tasks[task].thread = - 1;
	assert(workers[ret].used_as_preempt_ctx);
	workers[ret].used_as_preempt_ctx = false;
}

inline get_tid(cpu_id,ret) {
	assert(cpu_id != - 1);
	ret = - 1;

	byte i;
	for (i : 0 .. WORKER_NUM - 1) {
		if
		:: workers[i].executing_in == cpu_id -> 
			ret = i;
			break;
		:: else
		fi
	}
	
	assert(ret != - 1);
}

// awkernel_async_lib::task::do_preemption()
proctype interrupt_handler(int cpu_id) provided (interrupt_enabled[cpu_id]) {
	do
	:: ipi_requests[cpu_id]?_ -> 
		interrupted[cpu_id] = true;
		int tid;
		get_tid(cpu_id,tid);
		int cur_task = RUNNING[cpu_id];
		printf("Received IPI request. cpu_id = %d,cur_tid = %d,cur_task = %d\n",cpu_id,tid,cur_task);
		
		if
		:: cur_task == - 1 -> printf("There is no running task in cpu %d",cpu_id);goto finish;
		:: else
		fi
		
		lock(tid,lock_info[cur_task]);
		if
		:: !tasks[cur_task].need_preemption -> 
			unlock(tid,lock_info[cur_task]);
			printf("need_preemption is false: cpu_id = %d,cur_task = %d",cpu_id,cur_task);
			goto finish;
		:: else -> unlock(tid,lock_info[cur_task]);
		fi
		
		// If there is a task to be invoked next, execute the task.
		int hp_task;
		get_next_task(tid,hp_task);
		if
		:: hp_task == - 1 -> 
			printf("get_next_task() returns None: %d",cpu_id);
			goto finish;
		:: else
		fi
		
		printf("Preemption Occurs: cpu_id = %d,cur_task = %d,hp_task = %d\n",cpu_id,cur_task,hp_task);
		int next_thread;
		lock(tid,lock_info[hp_task]);
		if
		:: tasks[hp_task].thread != - 1 -> // preempted task
			take_preempt_context(hp_task,next_thread);
			unlock(tid,lock_info[hp_task]);
			yield_preempted_and_wake_task(cpu_id,cur_task,tid,next_thread);
		:: else -> // Otherwise,get a thread from the thread
			unlock(tid,lock_info[hp_task]);
			take_pooled_thread(next_thread);
			lock(tid,lock_next_task);
			assert(NEXT_TASK[cpu_id] == - 1);
			NEXT_TASK[cpu_id] = hp_task;
			unlock(tid,lock_next_task);
			yield_preempted_and_wake_task(cpu_id,cur_task,tid,next_thread);
		fi
		
		finish:
		interrupted[cpu_id] = false;
	od
}

inline yield_and_pool(cpu_id,cur_task,cur_tid,next_tid) {
	printf("yield_and_pool(): cpu_id = %d,cur_task = %d,cur_tid = %d,next_tid = %d\n",cpu_id,cur_task,cur_tid,next_tid);
	assert(!workers[cur_tid].used_as_preempt_ctx);
	context_switch(cpu_id,cur_tid,next_tid);
	wake_task(next_tid,cur_task);// re_schedule()
}

proctype run_main(int tid) provided (workers[tid].executing_in != - 1 && !interrupted[workers[tid].executing_in]) {
	start:
	if
	:: num_terminated == TASK_NUM -> goto end;
	:: else
	fi
	
	int task;
	atomic {
		get_next_task(tid,task);
	}
	
	if
	:: task == - 1 -> goto start;
	:: else -> skip;
	fi
	
	// If the next task is a preempted task, then the current task will yield to the thread holding the next task.
	// After that, the current thread will be stored in the thread pool.
	lock(tid,lock_info[task]);
	if
	:: tasks[task].thread != - 1 -> 
		int next_ctx;
		take_preempt_context(task,next_ctx);
		unlock(tid,lock_info[task]);
		yield_and_pool(workers[tid].executing_in,task,tid,next_ctx);
		goto start;
	:: else -> unlock(tid,lock_info[task]);
	fi
	
	try_lock(tid,lock_future[task]);
	
	if
	:: result_try_lock[tid] == false -> 
		// This task is running on another CPU,
		// and re-schedule the task to avoid starvation just in case.
		wake(tid,task);
		goto start;
	:: else -> skip;
	fi
	
	// Can remove this?
	if
	:: tasks[task].is_terminated -> 
		unlock(tid,lock_future[task]);
		goto start;
	:: else -> skip;
	fi
	
	lock(tid,lock_info[task]);
	
	if
	:: tasks[task].state == Terminated -> 
		unlock(tid,lock_info[task]);
		unlock(tid,lock_future[task]);
		goto start;
	:: else -> skip;
	fi
	
	unlock(tid,lock_info[task]);
	
	int cpu_id = workers[tid].executing_in;
	RUNNING[cpu_id] = task;
	
	// Invoke a task.
	mtype poll_result;
	interrupt_enabled[cpu_id] = true;
	future(tid,task,poll_result);
	interrupt_enabled[cpu_id] = false;
	unlock(tid,lock_future[task]);
	
	RUNNING[cpu_id] = - 1;

	lock(tid,lock_info[task]);
	if
	:: poll_result == Pending -> 
		printf("result_future Pending: tid = %d,task = %d\n",tid,task);
		tasks[task].state = Waiting;
		
		if
		:: tasks[task].need_sched -> 
			tasks[task].need_sched = false;
			unlock(tid,lock_info[task]);
			wake_task(tid,task);
			goto start;
		:: else -> skip;
		fi
	:: poll_result == Ready -> 
		printf("result_future Ready: tid = %d,task = %d\n",tid,task);
		if
		:: tasks[task].state != Terminated -> 
			num_terminated++;
		:: else -> assert(false);
		fi
		
		tasks[task].state = Terminated;
		tasks[task].is_terminated = true;
		
		printf("Terminated: tid = %d,task = %d,state = %e,num_terminated = %d,\n",tid,task,tasks[task].state,num_terminated);
	fi
	
	unlock(tid,lock_info[task]);
	
	goto start;
	
	end:
}


init {
	int i;
	
	for (i: 0 .. CPU_NUM - 1) {
		// HACK: interrupt_handlerが動いている際に、他のCPUのスレッドのrun_main()にも影響を及ぼす実装になっている。
		run interrupt_handler(i) priority 2;
	}
	
	for (i: 0 .. TASK_NUM - 1) {
		tasks[i].id = i;
		tasks[i].state = Ready;
		tasks[i].thread = - 1;
		
		wake(0,i);
	}
	
	
	for (i: 0 .. WORKER_NUM - 1) {
		workers[i].executing_in = - 1;
		workers[i].used_as_preempt_ctx = false;
		run run_main(i) priority 1;
	}
	
	for (i: 0 .. CPU_NUM - 1) {
		workers[i].executing_in = i;
	}
}

// - starvation-free
// - eventually all tasks will be terminated
ltl eventually_terminate {
	<> (num_terminated == TASK_NUM)
}
