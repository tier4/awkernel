bool future_blocked[TASK_NUM] = false

#if defined(KILL_TEST) || defined(KILL_RUNNING_PREEMPT_TEST)
// Kill-test variant: task 1 is the low-priority target, task 0 preempts it.
inline future(tid,task,ret) {
	printf("future(): tid = %d, task = %d\n", tid, task);
	if
	:: task == 1 ->
		wake(tid,0);
		future_blocked[1] = true;
		ret = Pending;
	:: task == 0 ->
		future_blocked[0] = true;
		ret = Ready;
	:: else -> assert(false);
	fi
}

#define INIT_TASK 1
#else
// This assumes that there are 4 tasks, with task IDs 0, 1, 2, and 3.
inline future(tid,task,ret) {
	printf("future(): tid = %d, task = %d\n", tid, task);
	if
	:: task == 2 -> // 2nd Low priority task
		if
		:: wake(tid,1); wake(tid,0);
		:: wake(tid,0); wake(tid,1);
		fi
		future_blocked[2] = true;
		ret = Ready;
	:: task == 3 -> // 1st Low priority task
		wake(tid,2);
		future_blocked[3] = true;
		ret = Ready;
	:: task == 0 -> // 1st High priority task
		if
		:: future_blocked[2] = true; future_blocked[3] = true;
		:: future_blocked[3] = true; future_blocked[2] = true;
		fi
		ret = Ready;
	:: task == 1 -> // 2nd High priority task
		if
		:: future_blocked[2] = true; future_blocked[3] = true;
		:: future_blocked[3] = true; future_blocked[2] = true;
		fi
		ret = Ready;
	:: else -> assert(false);
	fi
}

#define INIT_TASK 3
#endif
