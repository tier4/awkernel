#define TASK_NUM 4
#define WORKER_NUM TASK_NUM// Prepare same number of worker threads as tasks.
#define IR_HANDLER_NUM TASK_NUM// Prepare same number of interrupt handlers as tasks.
#ifndef CPU_NUM
#define CPU_NUM 2
#endif

#include "data_structure.pml"
#include "for_verification.pml"
#include "future_mock.pml"

inline min(a,b,ret) {
	d_step {
		if
		:: a < b -> ret = a
		:: else -> ret = b
		fi
	}
}

inline remove_from_ipi_requests(cpu_id,task) {
	d_step {
		byte k = 0;
		byte original_len = len(ipi_requests[cpu_id]);
		do
		:: k < original_len ->
			byte ipi_pending_task;
			ipi_requests[cpu_id]?ipi_pending_task;
			if
			:: ipi_pending_task != task -> ipi_requests[cpu_id]!ipi_pending_task;
			:: else -> printf("remove_from_ipi_requests(): remove task %d from ipi_requests[%d]\n",task,cpu_id)
			fi
			k++;
		:: else -> break
		od
	}
}

inline get_higher_priority_num_in_queue(task,ret) {
	d_step {
		byte k = 0;
		ret = 0;
		do
		:: k < len(queue) ->
			byte queued_task;
			queue?queued_task; queue!queued_task;
			if
			:: queued_task < task -> ret++;
			:: else
			fi
			k++;
		:: else -> break
		od
	}
}

inline get_lowest_priority_task(tid,task,ret_task,ret_cpu_id) {
	byte j;
	byte num_idle_cpus = 0;

	atomic {
		printf("get_lowest_priority_task(): tid = %d,task = %d\n",tid,task);
		for (j : 0 .. CPU_NUM - 1) {
			if
			:: RUNNING[j] == task ->// The task has already been running.
				assert(empty(ipi_requests[j]));
				ret_task = - 1;
				break
			:: RUNNING[j] == -1 ->
				assert(empty(ipi_requests[j]));
				num_idle_cpus++;
			:: else ->
				byte highest_pending;
				byte min_ret;
				if
				:: ipi_requests[j]?[highest_pending] -> 
					ipi_requests[j]?<highest_pending>;
					min(RUNNING[j],highest_pending,min_ret);
				:: else -> min_ret = RUNNING[j];
				fi

				if
				:: min_ret > ret_task -> 
					ret_task = min_ret;
					ret_cpu_id = j;
				:: else
				fi
			fi
		}
	}	

	byte higher_priority_num = 0;
	get_higher_priority_num_in_queue(ret_task,higher_priority_num);
	if
	:: higher_priority_num < num_idle_cpus ->
		ret_task = -1;
		ret_cpu_id = -1;
	:: else
	fi
}

inline set_need_preemption(tid,task) {
	lock(tid,lock_info[task]);
	tasks[task].need_preemption = true;
	unlock(tid,lock_info[task])
}

inline invoke_preemption(tid,task,ret) {
	int lp_task = - 1;
	int lp_cpu_id = - 1;
	get_lowest_priority_task(tid,task,lp_task,lp_cpu_id);
	if
	:: task < lp_task -> // If lp_task is - 1,preemption will not occur.
		set_need_preemption(tid,lp_task);
		atomic{
			printf("invoke_preemption() send IPI: hp_task = %d,lp_task = %d,lp_cpu_id = %d,interrupt_enabled[lp_cpu_id] = %d\n",task,lp_task,lp_cpu_id,interrupt_enabled[lp_cpu_id]);
			ipi_requests[lp_cpu_id]!!task
		}
		ret = true;
	:: else -> 
		d_step {
			printf("invoke_preemption() no need to preempt: hp_task = %d,lp_task = %d\n",task,lp_task);
			ret = false;
		}
	fi
}
	
/* awkernel_async_lib::scheduler::fifo::PrioritizedFIFOScheduler::wake_task()*/ 
inline wake_task(tid,task) {
	bool preemption_invoked;
	lock(tid,lock_queue);
	invoke_preemption(tid,task,preemption_invoked);
	if
	:: atomic{!preemption_invoked ->
		printf("wake_task(): push to queue: tid = %d,task = %d\n",tid,task);}
		queue!!task;
	:: else
	fi
	unlock(tid,lock_queue);
	d_step {
		assert(waking[task] > 0);
		waking[task]--;
	}
}

/* awkernel_async_lib::task::ArcWake::wake()*/ 
inline wake(tid,task) {
	waking[task]++;
	lock(tid,lock_info[task]);
	
	if
	:: tasks[task].state == Running || tasks[task].state == Runnable || tasks[task].state == Preempted -> 
		d_step{
			printf("wake() set need_sched: tid = %d,task = %d,state = %e\n",tid,task,tasks[task].state);
			tasks[task].need_sched = true;
			assert(waking[task] > 0);
			waking[task]--;
		}
		unlock(tid,lock_info[task])
	:: tasks[task].state == Terminated -> 
		d_step {
			printf("wake() already terminated: tid = %d,task = %d,state = %e\n",tid,task,tasks[task].state);
			assert(waking[task] > 0);
			waking[task]--;
		}
		unlock(tid,lock_info[task])
	:: tasks[task].state == Waiting || tasks[task].state == Ready -> 
		d_step {
			printf("wake() call wake_task(): tid = %d,task = %d,state = %e\n",tid,task,tasks[task].state);
			tasks[task].state = Runnable;
			update_runnable_preempted_highest_priority();
		}
		
		unlock(tid,lock_info[task]);
		wake_task(tid,task)
	fi
}

/* awkernel_async_lib::scheduler::fifo::PrioritizedFIFOScheduler::get_next()*/ 
inline scheduler_get_next(tid,ret) {
	lock(tid,lock_queue);
	
	byte head;
	
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
		
		d_step {
			printf("scheduler_get_next(): tid = %d,Chosen task = %d\n",tid,head);
			tasks[head].state = Running;
			update_runnable_preempted_highest_priority();
			update_running_lowest_priority();
		}
		d_step {
			printf("RUNNING[cpu_id(tid)] = task: cpu_id = %d,task = %d\n",cpu_id(tid),head);
			RUNNING[cpu_id(tid)] = head;
		}
		
		unlock(tid,lock_info[head]);
		unlock(tid,lock_queue);
		ret = head
	:: else -> 
		unlock(tid,lock_queue);
		ret = - 1
	fi
}

/* awkernel_async_lib::task::preempt::get_next_task()*/ 
inline preempt_get_next(tid,ret) {
	d_step { 
		if
		:: NEXT_TASK[cpu_id(tid)] != - 1 -> 
			ret = NEXT_TASK[cpu_id(tid)];
			NEXT_TASK[cpu_id(tid)] = - 1
		:: else
		fi
	}
}

/* awkernel_async_lib::task::get_next_task()*/ 
inline get_next_task(tid,ret) {
	preempt_get_next(tid,ret);
	if
	:: ret == - 1 -> 
		scheduler_get_next(tid,ret)
	:: else ->
		d_step {
			printf("RUNNING[cpu_id(tid)] = task: cpu_id = %d,task = %d\n",cpu_id(tid),ret);
			RUNNING[cpu_id(tid)] = ret;
		}
	fi
}

inline context_switch(cur_tid,next_tid) {
	d_step {
		assert(!workers[next_tid].pooled);
		assert(workers[next_tid].executing_in == -1);
		printf("context_switch(): cur_tid = %d,next_tid = %d\n",cur_tid,next_tid);
		workers[next_tid].executing_in = cpu_id(cur_tid);
		workers[cur_tid].executing_in = - 1
	}
}

inline set_preempt_context(task,tid) {
	d_step {
		tasks[task].thread = tid;
		workers[tid].used_as_preempt_ctx = true
	}
}

inline re_schedule(tid) {
	byte preempted;
	
	if
	:: atomic { PREEMPTED_TASK[cpu_id(tid)]?[preempted] -> PREEMPTED_TASK[cpu_id(tid)]?preempted;}
		wake_task(tid,preempted)
	:: else
	fi
}

inline yield_preempted_and_wake_task(cur_task,cur_tid,next_tid) {
	lock(cur_tid,lock_info[cur_task]);
	set_preempt_context(cur_task,cur_tid);
	d_step {
		tasks[cur_task].state = Preempted;
		update_runnable_preempted_highest_priority();
		update_running_lowest_priority();
	}
	unlock(cur_tid,lock_info[cur_task]);
	PREEMPTED_TASK[cpu_id(cur_tid)]!cur_task;
	
	d_step {
		handling_interrupt[cur_tid] = false;
		waking[cur_task]++;
		context_switch(cur_tid,next_tid);
	}
	re_schedule(cur_tid)
}

inline take_pooled_thread(ret) {
	d_step {
		ret = - 1;
		
		byte i;
		for (i : 0 .. WORKER_NUM - 1) {
			if
			:: (workers[i].pooled) -> 
				ret = i;
				workers[i].pooled = false;
				break;
			:: else
			fi
		}
		
		assert(ret != - 1)
		printf("take_pooled_thread(): ret_tid = %d\n",ret);
	}
}

inline take_preempt_context(task,ret) {
	d_step {
		ret = tasks[task].thread;
		tasks[task].thread = - 1;
		assert(workers[ret].executing_in == - 1);
		assert(workers[ret].used_as_preempt_ctx);
		workers[ret].used_as_preempt_ctx = false;
	}
}

/* 
* kernel::x86_64::interrupt_handler::preemption() ~ awkernel_async_lib::task::do_preemption()
* In this model,Worker and InterruptHandler has one-to-one relationship, so tid equals the interrupt handler's id.
*/ 
proctype interrupt_handler(byte tid) provided (workers[tid].executing_in != - 1) {
	byte cpu_id;
	short cur_task;
	short hp_task;
	short next_thread;
	byte pending_lp_task;
	
	do
	:: d_step {interrupt_enabled[cpu_id(tid)] && nempty(ipi_requests[cpu_id(tid)]) -> 
			ipi_requests[cpu_id(tid)]?<hp_task>;
			cpu_id = cpu_id(tid);
			printf("Received IPI request. cpu_id = %d\n",cpu_id);
			interrupt_enabled[cpu_id] = false;
			workers[tid].interrupted = true;
			handling_interrupt[tid] = true;
		}
		
		cur_task = RUNNING[cpu_id];
		if
		:: d_step{cur_task == - 1 -> 
			printf("There is no running task in cpu_id %d\n",cpu_id);}
			d_step {
				remove_from_ipi_requests(cpu_id,hp_task);
				waking[hp_task]++;
			}
			wake_task(tid,hp_task);
			goto finish
		:: else
		fi
		
		if
		:: d_step{cur_task < hp_task ->
			printf("cur_task < hp_task: cpu_id = %d,cur_task = %d,hp_task = %d\n",cpu_id,cur_task,hp_task);}
			d_step {
				remove_from_ipi_requests(cpu_id,hp_task);
				waking[hp_task]++;
			}
			wake_task(tid,hp_task);
			goto finish;
		:: else
		fi
		
		// If there is a task to be invoked next, execute the task.
		atomic {
			printf("RUNNING[cpu_id] = hp_task: cpu_id = %d,hp_task = %d\n",cpu_id,hp_task);
			RUNNING[cpu_id] = hp_task;
		}
		remove_from_ipi_requests(cpu_id,hp_task);

		// Re-wake the remaining all preemption-pending tasks with lower priorities than `next`.
		do
		:: atomic {ipi_requests[cpu_id]?[pending_lp_task] -> ipi_requests[cpu_id]?pending_lp_task;
			waking[pending_lp_task]++;}
			wake_task(tid,pending_lp_task)
		:: atomic{else -> break}
		od
		
		printf("Preemption Occurs: cpu_id = %d,cur_task = %d,hp_task = %d\n",cpu_id,cur_task,hp_task);
		lock(tid,lock_info[hp_task]);
		if
		:: d_step { tasks[hp_task].thread != - 1 -> take_preempt_context(hp_task,next_thread);}
			unlock(tid,lock_info[hp_task]);
			yield_preempted_and_wake_task(cur_task,tid,next_thread);
		:: else -> // Otherwise,get a thread from the thread pool or create a new thread.
			unlock(tid,lock_info[hp_task]);
			take_pooled_thread(next_thread);
			d_step {
				assert(NEXT_TASK[cpu_id] == - 1);
				NEXT_TASK[cpu_id] = hp_task;
			}
			yield_preempted_and_wake_task(cur_task,tid,next_thread);
		fi
		
		finish:
		atomic {
			interrupt_enabled[cpu_id(tid)] = true;// iretq
			workers[tid].interrupted = false
			handling_interrupt[tid] = false;
		}
	od
}

inline yield_and_pool(cur_task,cur_tid,next_tid) {
	d_step {
		printf("yield_and_pool(): cur_task = %d,cur_tid = %d,next_tid = %d\n",cur_task,cur_tid,next_tid);
		assert(workers[cur_tid].executing_in != - 1);
		assert(!workers[cur_tid].used_as_preempt_ctx);
		workers[cur_tid].pooled = true;
		context_switch(cur_tid,next_tid);
	}
	re_schedule(cur_tid)
}

proctype run_main(byte tid) provided (workers[tid].executing_in != - 1 && !workers[tid].interrupted && !wait_for_weak_fairness[tid]) {
	printf("proc %d (run_main), tid = %d\n", _pid, tid);
	if
	:: tid >= CPU_NUM -> re_schedule(tid);// thread_entry();
	:: else
	fi
	
	mtype poll_result;
	
	start:
	atomic {
		consecutive_run_main_loop[tid]++;
		if
		:: consecutive_run_main_loop[tid] == MAX_CONSECUTIVE_RUN_MAIN_LOOP ->
			printf("consecutive_run_main_loop[%d] == MAX_CONSECUTIVE_RUN_MAIN_LOOP\n",tid);
			resume_requests!tid;
			wait_for_weak_fairness[tid] = true;
		:: else
		fi
	}

	if
	:: RUNNING[cpu_id(tid)] == - 1 -> 
		byte pending_task;
		do
		:: atomic {ipi_requests[cpu_id(tid)]?[pending_task] -> ipi_requests[cpu_id(tid)]?pending_task;
			waking[pending_task]++;}
			wake_task(tid,pending_task)
		:: atomic{else -> break}
		od
	:: else
	fi

	if
	:: num_terminated == TASK_NUM -> goto end;
	:: else
	fi
	
	short task = - 1;
	get_next_task(tid,task);
	
	if
	:: task == - 1 -> goto start;
	:: d_step{else -> consecutive_run_main_loop[tid] = 0;}
	fi
	
	// If the next task is a preempted task, then the current task will yield to the thread holding the next task.
	// After that, the current thread will be stored in the thread pool.
	lock(tid,lock_info[task]);
	if
	:: tasks[task].thread != - 1 -> 
		byte next_ctx;
		take_preempt_context(task,next_ctx);
		unlock(tid,lock_info[task]);
		yield_and_pool(task,tid,next_ctx);
		goto start;
	:: else -> unlock(tid,lock_info[task]);
	fi

	// Invoke a task.
	interrupt_enabled[cpu_id(tid)] = true;
	future(tid,task,poll_result);
	interrupt_enabled[cpu_id(tid)] = false;
	
	d_step {
		assert(RUNNING[cpu_id(tid)] == task);
		printf("RUNNING[cpu_id(tid)] = -1: cpu_id = %d\n",cpu_id(tid));
		RUNNING[cpu_id(tid)] = - 1;
	}
	
	lock(tid,lock_info[task]);
	if
	:: d_step{poll_result == Pending -> 
		printf("result_future Pending: tid = %d,task = %d\n",tid,task);}
		d_step {
			tasks[task].state = Waiting;
			update_running_lowest_priority();
		}
		
		if
		:: tasks[task].need_sched -> 
			tasks[task].need_sched = false;
			unlock(tid,lock_info[task]);
			wake(tid,task);
			goto start;
		:: else;
		fi
	:: d_step{poll_result == Ready -> 
		printf("result_future Ready: tid = %d,task = %d\n",tid,task);}
		if
		:: tasks[task].state != Terminated -> 
			num_terminated++;
		:: else -> assert(false);
		fi
		
		d_step {
			tasks[task].state = Terminated;
			update_running_lowest_priority();
			printf("Terminated: tid = %d,task = %d,state = %e,num_terminated = %d,\n",tid,task,tasks[task].state,num_terminated);
		}
	fi
	
	unlock(tid,lock_info[task]);
	
	goto start;
	
	end:
}


init {
	byte i;

	for (i: 0 .. TASK_NUM - 1) {
		tasks[i].id = i;
	}
	
	wake(0,3);

	for (i: 0 .. IR_HANDLER_NUM - 1) {
		run interrupt_handler(i);
	}
	
	for (i: 0 .. WORKER_NUM - 1) {
		run run_main(i);
	}
	
	atomic {
		for (i: 0 .. CPU_NUM - 1) {
			workers[i].pooled = false;
			workers[i].executing_in = i;
		}
	}
}

#include "ltl.pml"
