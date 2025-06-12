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
		:: else -> ret_task = - 1;break;
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
	:: task < lp_task -> // If lp_task is - 1,preemption will not occur.
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
	waking[task] = false;
}

/* awkernel_async_lib::task::ArcWake::wake() */
inline wake(tid,task) {
	waking[task] = true;
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
		atomic {
			tasks[task].state = Runnable;
			update_runnable_highest_priority();
		}

		unlock(tid,lock_info[task]);
		wake_task(tid,task);
	fi
}
