#define TASK_NUM 4
#define WORKERS 2// ワーカスレッドの数。これらは特に制約無く実行されるので、実質CPUの数とみなせる。
#define NUM_PROC WORKERS

#include "../cooperative_spin/fair_lock.pml"

mtype = { Ready,Runnable,Running,Waiting,Terminated,Pending,Preempted };// Panickedは無視されている。

// awkernel_async_lib::task::TaskInfo
typedef TaskInfo {
	mtype state;
	bool need_sched;
	bool is_terminated;
	int id;  // これを優先度としても扱う。小さいほど高優先度。
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

// awkernel_async_lib::scheduler::fifo::PrioritizedFIFOScheduler::wake_task()
// - task: int. TaskInfoのID、すなわち、タスクID
// - tid: int. WORKERSのID、すなわち、スレッドID
inline wake_task(tid,task) {
	lock(tid,lock_scheduler);
	queue!!task;

	// TODO: invoke preemption.

	unlock(tid,lock_scheduler);
}

// awkernel_async_lib::task::ArcWake::wake()
inline wake(tid,task) {
	lock(tid,lock_info[task]);
	
	if
	:: tasks[task].state == Running || tasks[task].state == Runnable -> 
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
		:: else -> skip;  // これが無いと処理が進まない。
		fi
		
		tasks[head].state = Running;
		
		printf("Running: task = %d,state = %d\n",head,tasks[head].state);
		
		unlock(tid,lock_info[head]);
		unlock(tid,lock_scheduler);
		
		result_next[tid] = head;
	:: else -> // queue内に実行可能なタスクが無い場合
		unlock(tid,lock_scheduler);
		result_next[tid] = - 1;
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
// これはおそらくタスクの処理を模倣する関数
inline future(tid,task) {
	if
	:: task >= TASK_NUM / 2 -> // 上の例で言うstep2
		wake(tid,task - TASK_NUM / 2);
		result_future[tid] = Ready;
	:: else -> 
		if
		:: wake_other[task] -> //上の例で言うstep3
// wake(task);
			result_future[tid] = Ready;
			printf("future(): tid = %d,task = %d\n",tid,task);
		:: else -> //上の例で言うstep1
			wake(tid,task + TASK_NUM / 2);
			wake_other[task] = true;
			result_future[tid] = Pending;
		fi
	fi
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
	
// tasks[task].need_sched = false;
	
	printf("execute task = %d\n",task);
	
// Invoke a task.
	future(tid,task);
	
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
		
		printf("tasks[%d].state = %d\n",i,tasks[i].state);
		
		wake(0,i);
	}
	
	for (i: 0 .. WORKERS - 1) {
		run run_main(i);
	}
}

// - starvation-free
// - eventually all tasks will be terminated
ltl eventually_terminate {
	<> (num_terminated == TASK_NUM)
}
