#define TASK_NUM 4
#define WORKERS TASK_NUM// ワーカスレッドの数。各futureにつき１つ用意する。
#define CPU_NUM 2
#define NUM_PROC WORKERS

#include "../cooperative_spin/fair_lock.pml"

// NOTE: 計算量爆発する場合は、これらのロックをまとめることを検討。
FairLock lock_info[TASK_NUM];// TaskInfoに対するロック
FairLock lock_future[TASK_NUM];// Task.futureに対するロック。struct TaskはTaskInfoとfutureを持つ
FairLock lock_scheduler = false;// スケジューラのqueueに対するロック

int worker_executing[WORKERS] = - 1;// worker_id -> cpu_id. 実行されていない場合は - 1が入る。各ワーカスレッドが現在コア上で実行中かどうかのフラグ。これは実装に無い。
bool worker_attached[WORKERS] = false;// ワーカスレッドがタスクにアタッチされているかどうかのフラグ。
int running_tasks[CPU_NUM] = - 1;// cpu_id -> task_id。 - 1の場合は実行中のタスクが無いことを示す。
int next_tasks[CPU_NUM] = - 1;// プリエンプション用のタスク置き場。
bool interrupted[CPU_NUM] = false;// 割り込みを実行中かのフラグ。

inline get_running_num(ret) {
	ret = 0;
	int j;
	for (j : 0 .. CPU_NUM - 1) {
		if
		:: running_tasks[j] != - 1 -> 
			ret++;
		:: else
		fi
	}
}

inline get_tid(cpu_id,ret) {
	assert(cpu_id != - 1);
	ret = - 1;
	int i;
	for (i : 0 .. WORKERS - 1) {
		if
		:: worker_executing[i] == cpu_id -> 
			ret = i;
			break;
		:: else
		fi
	}
	
	assert(ret != - 1);
}

mtype = { Ready,Runnable,Running,Waiting,Terminated,Pending,Preempted };// Panickedは無視されている。

// awkernel_async_lib::task::TaskInfo
typedef TaskInfo {
	mtype state;
	bool need_sched;
	bool is_terminated;
	int id;// これを優先度としても扱う。小さいほど高優先度。
	bool need_preemption;
	int thread;// tid.プリエンプトされた場合、ワーカスレッドをコンテキストとして持つ。それ以外は - 1
};

TaskInfo tasks[TASK_NUM];

// Queue of the PrioritizedFIFO scheduler
chan queue = [TASK_NUM * 2] of { int };// これにはタスクIDが入る。タスクID = priorityとみなす。

// 関数の返り値をグローバル変数に格納するスタイルで書かれている。
int result_next[WORKERS];// tid -> get_next()の結果を格納する。これはタスクIDが入る
mtype result_future[WORKERS];// tid -> future()の結果を格納する。これはReadyかPendingが入る

bool wake_other[TASK_NUM / 2];// 他のタスクをwakeしたかどうかのフラグ。wakeしてる場合は、そのタスクがReadyになるまではPendingになる。
int num_terminated = 0;// 検証のための変数。

chan ipi_requests[CPU_NUM] = [WORKERS] of { int };// IPIリクエストを受け取るチャネル。intはとりあえずタスクID。
bool interrupt_enabled[CPU_NUM] = false;

inline get_lowest_priority_task(ret_task,ret_cpu_id) {
	int k;
	ret_task = - 1;
	for (k : 0 .. CPU_NUM - 1) {
		if
		:: running_tasks[k] != - 1 -> 
			if
			:: running_tasks[k] > ret_task -> ret_task = running_tasks[k];ret_cpu_id = k;
			:: else
			fi
		:: else
		fi
	}
}

inline invoke_preemption(task) {
	int running_num;
	get_running_num(running_num);
	if
	:: running_num < CPU_NUM -> 
		goto finish_invoke_preemption;
	:: else
	fi
	
	int lp_task;
	int lp_cpu_id;
	get_lowest_priority_task(lp_task,lp_cpu_id);
	if
	:: task < lp_task -> 
		tasks[lp_task].need_preemption = true;
		printf("invoke_preemption() send IPI: hp_task = %d,lp_task = %d,lp_cpu_id = %d,interrupt_enabled[lp_cpu_id] = %d\n",task,lp_task,lp_cpu_id,interrupt_enabled[lp_cpu_id]);
		ipi_requests[lp_cpu_id]!task;// interrupt_enabled[lp_cpu_id]がfalseの可能性はある。
	:: else
	fi
	
	finish_invoke_preemption:
}

// awkernel_async_lib::scheduler::fifo::PrioritizedFIFOScheduler::wake_task()
inline wake_task(tid,task) {
	lock(tid,lock_scheduler);
	queue!!task;
	unlock(tid,lock_scheduler);
	
	invoke_preemption(task);
}

// awkernel_async_lib::task::ArcWake::wake()
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

// awkernel_async_lib::scheduler::fifo::FIFOScheduler::get_next()
inline scheduler_get_next(tid) {
	lock(tid,lock_scheduler);
	
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
		unlock(tid,lock_scheduler);
		
		result_next[tid] = head;
	:: else -> // queue内に実行可能なタスクが無い場合
		unlock(tid,lock_scheduler);
		result_next[tid] = - 1;
	fi
}

// awkernel_async_lib::task::get_next_task()
inline get_next(tid) {
	int _cpu_id = worker_executing[tid];
	assert(_cpu_id != - 1);
	if
	:: next_tasks[_cpu_id] != - 1 -> 
		result_next[tid] = next_tasks[_cpu_id];
		next_tasks[_cpu_id] = - 1;
	:: else -> 
		scheduler_get_next(tid);
	fi
}

// If there is 2 tasks, and their task ID's are 0 and 1.
// This future will execute as follows.
//
// step1: Task 0 wakes Task 1 up, and returns "Pending".
// step2: Task 1 wakes Task 0 up, and returns "Ready".
// step3: Task 0 returns "Ready".
//
// A task will become "Terminated", after returning "Ready".
inline future(tid,task) {
	if
	:: task >= TASK_NUM / 2 -> 
		wake(tid,task - TASK_NUM / 2);
		result_future[tid] = Ready;
	:: else -> 
		if
		:: wake_other[task] -> 
			result_future[tid] = Ready;
			printf("future(): tid = %d,task = %d\n",tid,task);
		:: else -> 
			wake(tid,task + TASK_NUM / 2);
			wake_other[task] = true;
			result_future[tid] = Pending;
		fi
	fi
}

inline context_switch(cpu_id,cur_tid,next_tid) {
	printf("context_switch(): cpu_id = %d,cur_tid = %d,next_tid = %d\n",cpu_id,cur_tid,next_tid);
	assert(worker_executing[cur_tid] == cpu_id);
	worker_executing[next_tid] = cpu_id;
	worker_executing[cur_tid] = - 1;
}

inline yield_preempted_and_wake_task(cpu_id,cur_task,cur_tid,next_tid) {
	lock(cur_tid,lock_info[cur_task]);
	tasks[cur_task].thread = cur_tid;
	tasks[cur_task].state = Preempted;
	unlock(cur_tid,lock_info[cur_task]);
	worker_attached[cur_tid] = true;
	context_switch(cpu_id,tasks[cur_task].thread,next_tid);
	wake_task(next_tid,cur_task);// re_schedule()
}

inline take_pooled_thread(ret) {
	ret = - 1;
	int k;
	for (k : 0 .. WORKERS - 1) {
		if
		:: (worker_executing[k] == - 1 && !worker_attached[k]) -> 
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
	assert(worker_attached[ret])
	worker_attached[ret] = false;
}

// awkernel_async_lib::task::do_preemption()
proctype interrupt_handler(int cpu_id) provided (interrupt_enabled[cpu_id]) {
	do
	:: ipi_requests[cpu_id]?_ -> 
		interrupted[cpu_id] = true;
		int tid;
		get_tid(cpu_id,tid);
		int cur_task = running_tasks[cpu_id];
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
		get_next(tid);
		int hp_task = result_next[tid];
		if
		:: hp_task == - 1 -> 
			printf("get_next() returns None: %d",cpu_id);
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
			assert(next_tasks[cpu_id] == - 1);
			next_tasks[cpu_id] = hp_task;
			yield_preempted_and_wake_task(cpu_id,cur_task,tid,next_thread);
		fi
		
		finish:
		interrupted[cpu_id] = false;
	od
}

inline yield_and_pool(cpu_id,cur_task,cur_tid,next_tid) {
	printf("yield_and_pool(): cpu_id = %d,cur_task = %d,cur_tid = %d,next_tid = %d\n",cpu_id,cur_task,cur_tid,next_tid);
	assert(!worker_attached[cur_tid]);
	context_switch(cpu_id,cur_tid,next_tid);
	wake_task(next_tid,cur_task);// re_schedule()
}

proctype run_main(int tid) provided (worker_executing[tid] != - 1 && !interrupted[worker_executing[tid]]) {
	start:
	if
	:: num_terminated == TASK_NUM -> goto end;
	:: else
	fi
	
	int task;
	atomic {
		get_next(tid);
		task = result_next[tid];
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
		yield_and_pool(worker_executing[tid],task,tid,next_ctx);
		goto start;
	:: else -> unlock(tid,lock_info[task]);
	fi
	
	try_lock(tid,lock_future[task]);
	
	if
	:: result_try_lock[tid] == false -> 
		// This task is running_tasks on another CPU,
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
	
	int cpu_id = worker_executing[tid];
	running_tasks[cpu_id] = task;
	
	// Invoke a task.
	interrupt_enabled[cpu_id] = true;
	future(tid,task);
	interrupt_enabled[cpu_id] = false;
	
	unlock(tid,lock_future[task]);
	
	lock(tid,lock_info[task]);
	
	running_tasks[cpu_id] = - 1;
	
	if
	:: result_future[tid] == Pending -> 
		printf("result_future Pending: tid = %d,task = %d\n",tid,task);
	:: result_future[tid] == Ready -> 
		printf("result_future Ready: tid = %d,task = %d\n",tid,task);
	fi
	
	if
	:: result_future[tid] == Pending -> 
		tasks[task].state = Waiting;
		
		if
		:: tasks[task].need_sched -> 
			tasks[task].need_sched = false;
			unlock(tid,lock_info[task]);
			wake_task(tid,task);
			goto start;
		:: else -> skip;
		fi
	:: result_future[tid] == Ready -> 
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
	
	
	for (i: 0 .. WORKERS - 1) {
		run run_main(i) priority 1;
	}
	
	for (i: 0 .. CPU_NUM - 1) {
		worker_executing[i] = i;
	}
}

// - starvation-free
// - eventually all tasks will be terminated
ltl eventually_terminate {
	<> (num_terminated == TASK_NUM)
}
