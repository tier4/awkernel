bool wake_other[TASK_NUM / 2];

// If there is 2 tasks, and their task ID's are 0 and 1.
// This future will execute as follows.
//
// step1: Task 0 wakes Task 1 up, and returns "Pending".
// step2: Task 1 wakes Task 0 up, and returns "Ready".
// step3: Task 0 returns "Ready".
//
// A task will become "Terminated", after returning "Ready".
inline future(tid,task,ret) {
	if
	:: task >= TASK_NUM / 2 -> 
		wake(tid,task - TASK_NUM / 2);
		ret = Ready;
	:: else -> 
		if
		:: wake_other[task] -> 
			ret = Ready;
			printf("future(): tid = %d,task = %d\n",tid,task);
		:: else -> 
			wake(tid,task + TASK_NUM / 2);
			wake_other[task] = true;
			ret = Pending;
		fi
	fi
}
