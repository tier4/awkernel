#define TASK_NUM 4
#define WORKERS 2// ワーカスレッドの数。これらは特に制約無く実行されるので、CPUを専有しており、実質CPUの数とみなせる。
#define NUM_PROC WORKERS

#include "../cooperative_spin/fair_lock.pml"

mtype = { Ready,Runnable,Running,Waiting,Terminated,Pending,Preempted };// Panickedは無視されている。

// awkernel_async_lib::task::TaskInfo
typedef TaskInfo {
	mtype state;
	bool need_sched;
	bool is_terminated;
	int id;  // これを優先度としても扱う。小さいほど高優先度。
	bool need_preemption;
	int tid; // このタスクを実行しているスレッドID。Awkernelには無いが、検証のために追加している。
};

TaskInfo tasks[TASK_NUM];

// Queue of the PrioritizedFIFO scheduler
chan queue = [TASK_NUM * 2] of { int }; // これにはタスクIDが入る。タスクID=priorityとみなす。

// NOTE: 計算量爆発する場合は、これらのロックをまとめることを検討。
FairLock lock_info[TASK_NUM];// TaskInfoに対するロック
FairLock lock_future[TASK_NUM];// Task.futureに対するロック。struct TaskはTaskInfoとfutureを持つ
FairLock lock_scheduler = false;// スケジューラのqueueに対するロック

// 関数の返り値をグローバル変数に格納するスタイルで書かれている。
int result_next[WORKERS];// get_next()の結果を格納する。これはタスクIDが入る
mtype result_future[WORKERS];// future()の結果を格納する。これはReadyかPendingが入る

bool wake_other[TASK_NUM / 2];// 他のタスクをwakeしたかどうかのフラグ。wakeしてる場合は、そのタスクがReadyになるまではPendingになる。

int num_terminated = 0;// 検証のための変数。

inline get_running_num(count) {
	count = 0;
	int j;
	for (j : 0 .. TASK_NUM - 1) {
		if
		:: tasks[j].state == Running -> count++;
		:: else -> skip;
		fi
	}	
}

chan ipi_requests[WORKERS] = [WORKERS] of { int }; // IPIリクエストを受け取るチャネル。intはとりあえずタスクID。
bool interrupt_enabled[WORKERS] = false;

inline get_lowest_priority_task(ret_task, ret_tid) {
	int k;
	ret_task = -1;
	for (k : 0 .. TASK_NUM - 1) {
		if
		:: tasks[k].state == Running -> 
			if
			:: tasks[k].id > ret_task -> ret_task = tasks[k].id; ret_tid = tasks[k].tid;
			:: else -> skip;
			fi
		:: else -> skip;
		fi
	}
}

// task: idであり、優先度。
inline invoke_preemption(task) {
	int running_num;
	get_running_num(running_num);
	if
	:: running_num < WORKERS -> 
		goto finish;
	:: else -> skip;
	fi

	int lp_task;
	int lp_tid;
	get_lowest_priority_task(lp_task, lp_tid);
	if
	:: task < lp_task -> 
		tasks[lp_task].need_preemption = true;
		printf("invoke_preemption: task = %d, lp_task = %d, lp_tid = %d\n",task,lp_task,lp_tid);
		ipi_requests[lp_tid]!task;
	:: else -> skip;
	fi

	finish:
}

// awkernel_async_lib::scheduler::fifo::PrioritizedFIFOScheduler::wake_task()
// - task: int. TaskInfoのID、すなわち、タスクID
// - tid: int. WORKERSのID、すなわち、スレッドID
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
		printf("wake(): task = %d,state = %d\n",task,tasks[task].state);
		unlock(tid,lock_info[task]);
	:: tasks[task].state == Terminated -> unlock(tid,lock_info[task]);
	:: tasks[task].state == Waiting || tasks[task].state == Ready -> 
		printf("wake(): task = %d,state = %d\n",task,tasks[task].state);
		tasks[task].state = Runnable;
		unlock(tid,lock_info[task]);
		wake_task(tid,task);
	fi
}

// awkernel_async_lib::scheduler::fifo::FIFOScheduler::get_next()
inline get_next(tid) {
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
		:: else -> skip;  // これが無いと処理が進まない。
		fi
		
		tasks[head].state = Running;
		tasks[head].tid = tid;
		
		printf("Running: task = %d,state = %d\n",head,tasks[head].state);
		
		unlock(tid,lock_info[head]);
		unlock(tid,lock_scheduler);
		
		result_next[tid] = head;
	:: else -> // queue内に実行可能なタスクが無い場合
		unlock(tid,lock_scheduler);
		result_next[tid] = - 1;
	fi
}

int future_tid[TASK_NUM] = -1; // task id -> future()を実行しているtid。-1である場合、実行されていない。

// If there is 2 tasks, and their task ID's are 0 and 1.
// This future will execute as follows.
//
// step1: Task 0 wakes Task 1 up, and returns "Pending".
// step2: Task 1 wakes Task 0 up, and returns "Ready".
// step3: Task 0 returns "Ready".
//
// A task will become "Terminated", after returning "Ready".
proctype future(int task) provided (future_tid[task] != -1) {
	printf("[future]: task = %d, future_tid[task] = %d\n",task,future_tid[task]);
	if
	:: task >= TASK_NUM / 2 -> // 上の例で言うstep2
		wake(future_tid[task],task - TASK_NUM / 2);
		result_future[future_tid[task]] = Ready
	:: else -> 
		if
		:: wake_other[task] -> //上の例で言うstep3
			result_future[future_tid[task]] = Ready;
		:: else -> //上の例で言うstep1
			wake(future_tid[task],task + TASK_NUM / 2);
			wake_other[task] = true;
			result_future[future_tid[task]] = Pending;
		fi
	fi

	future_tid[task] = -1;
}

proctype interrupt_handler(int tid) provided (interrupt_enabled[tid]) {
	int hp_task;
	do
    :: ipi_requests[tid]?_ ->
		printf("interrupt_handler: tid = %d, received IPI request\n",tid);
		int cur_task = result_next[tid];
	    if
		:: (tasks[cur_task].state != Running || !tasks[cur_task].need_preemption) -> 
			printf("state: %d, need_preemption: %d\n",tasks[cur_task].state,tasks[cur_task].need_preemption);
			assert(false);
		:: else ->
			get_next(tid);
			hp_task = result_next[tid];
			assert(hp_task != -1);
			future_tid[cur_task] = -1;
			// TODO: lock for task
			future_tid[hp_task] = tid;
			lock(tid,lock_info[cur_task]);
			tasks[cur_task].state = Preempted;
			unlock(tid,lock_info[cur_task]);
			wake(tid,cur_task);
		fi
	od
}

proctype run_main(int tid) {
	start:
	if
	:: num_terminated == TASK_NUM -> goto end;
	:: else -> skip;
	fi
	
	get_next(tid);
	
	int task = result_next[tid];
	
	if
	:: task == - 1 -> goto start;
	:: else -> skip;
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
	
	printf("execute task = %d\n",task);
	
	// Invoke a task.
    interrupt_enabled[tid] = true;
	future_tid[task] = tid;
	interrupt_enabled[tid] = false;
	
	unlock(tid,lock_future[task]);
	
	lock(tid,lock_info[task]);
	
	if
	:: result_future[tid] == Pending -> 
		printf("Pending: tid = %d\n",tid);
	:: result_future[tid] == Ready -> 
		printf("Ready: tid = %d\n",tid);
	fi
	
	if
	:: result_future[tid] == Pending -> 
		tasks[task].state = Waiting;
		
		printf("Waiting: task = %d,state = %d\n",task,tasks[task].state);
		
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
		:: else -> skip;
		fi
		
		tasks[task].state = Terminated;
		tasks[task].is_terminated = true;
		
		printf("Terminated: task = %d,state = %d,num_terminated = %d,\n",task,tasks[task].state,num_terminated);
	fi
	
	unlock(tid,lock_info[task]);
	
	goto start;
	
	end:
}


init {
	int i;
	
	for (i: 0 .. TASK_NUM - 1) {
		tasks[i].id = i;
		tasks[i].state = Ready;
		
		wake(0,i);

		run future(i) priority 2;
	}

	for (i: 0 .. WORKERS - 1) {
		run interrupt_handler(i) priority 3;
	}
	
	for (i: 0 .. WORKERS - 1) {
		run run_main(i) priority 1;
	}
}

// - starvation-free
// - eventually all tasks will be terminated
ltl eventually_terminate {
	<> (num_terminated == TASK_NUM)
}
