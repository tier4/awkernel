int num_terminated = 0

bool waking[TASK_NUM] = false

short runnable_preempted_highest_priority = 99
short running_lowest_priority = - 99

inline update_runnable_preempted_highest_priority() {
	atomic {
		runnable_preempted_highest_priority = 99;
		byte j;
		for (j: 0 .. TASK_NUM - 1) {
			if
			:: ((tasks[j].state == Runnable || tasks[j].state == Preempted) && tasks[j].id < runnable_preempted_highest_priority) -> 
				runnable_preempted_highest_priority = tasks[j].id
			:: else
			fi
		}
	}
}

inline update_running_lowest_priority() {
	atomic {
		running_lowest_priority = - 99;
		byte j;
		for (j: 0 .. TASK_NUM - 1) {
			if
			:: (tasks[j].state == Running && tasks[j].id > running_lowest_priority) -> 
				running_lowest_priority = tasks[j].id
			:: else
			fi
		}
	}
}
