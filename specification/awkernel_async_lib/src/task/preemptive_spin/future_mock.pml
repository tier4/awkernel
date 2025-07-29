bool future_blocked[TASK_NUM] = false

// This assumes that there are 5 tasks, with task IDs 0, 1, 2, 3, and 4.
inline future(tid,task,ret) {
	printf("future(): tid = %d, task = %d\n", tid, task);
	if
	:: task == 3 -> // 2nd Low priority task
		wake(tid,2);
		wake(tid,1);
		wake(tid,0);

		future_blocked[3];
		ret = Ready
	:: task == 4 -> // 1st Low priority task
		wake(tid,3);
		future_blocked[4];
		ret = Ready
	:: task == 0 -> // 1st High priority task
		ret = Ready
	:: task == 1 -> // 2nd High priority task
		ret = Ready
	:: task == 2 -> // 3rd High priority task
		if
		:: future_blocked[3] = true; future_blocked[4] = true;
		:: future_blocked[4] = true; future_blocked[3] = true;
		fi
		ret = Ready
	:: else -> assert(false);
	fi
}
