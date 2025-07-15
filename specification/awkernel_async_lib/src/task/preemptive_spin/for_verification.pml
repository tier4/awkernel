int num_terminated = 0

byte waking[TASK_NUM] = 0
bool handling_interrupt[IR_HANDLER_NUM] = false

short runnable_preempted_highest_priority = BYTE_MAX
short running_lowest_priority = - BYTE_MAX

#define MAX_CONSECUTIVE_RUN_MAIN_LOOP 5
byte consecutive_run_main_loop[WORKER_NUM] = 0
bool wait_for_weak_fairness[WORKER_NUM] = false

proctype wait_until_timeout(byte tid) {
	if
	:: timeout -> d_step{wait_for_weak_fairness[tid] = false; consecutive_run_main_loop[tid] = 0;}
	fi
}

inline update_runnable_preempted_highest_priority() {
	d_step {
		runnable_preempted_highest_priority = BYTE_MAX;
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
	d_step {
		running_lowest_priority = - BYTE_MAX;
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
