byte num_terminated = 0

byte waking[TASK_NUM] = 0
bool handling_interrupt[IR_HANDLER_NUM] = false

byte runnable_preempted_highest_priority = BYTE_MAX
short running_lowest_priority = - BYTE_MAX

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

#define MAX_CONSECUTIVE_RUN_MAIN_LOOP 2
byte consecutive_run_main_loop[WORKER_NUM] = 0
bool wait_for_weak_fairness[WORKER_NUM] = false
chan resume_requests = [WORKER_NUM] of { byte }// tid that requested to resume execution.

active proctype timeout_handler() {
	xr resume_requests;
	byte tid;
	
	do
	:: timeout -> 
		if
		:: num_terminated == TASK_NUM -> break
		:: atomic{else -> 
				assert(nempty(resume_requests));
				resume_requests?tid;
				assert(wait_for_weak_fairness[tid]);
				wait_for_weak_fairness[tid] = false;
				assert(consecutive_run_main_loop[tid] == MAX_CONSECUTIVE_RUN_MAIN_LOOP);
				consecutive_run_main_loop[tid] = 0;
			}
		fi
	od
}
