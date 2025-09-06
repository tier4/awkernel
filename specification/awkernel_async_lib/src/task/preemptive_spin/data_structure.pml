typedef Worker {
	short executing_in = - 1;// cpu_id when this is executed, -1 otherwise.
	bool used_as_preempt_ctx = false;
	bool interrupted = false;
	bool pooled = true;
}

Worker workers[WORKER_NUM]

mtype = { Ready,Runnable,Running,Waiting,Terminated,Pending,Preempted }// Panic is not considered.

/* awkernel_async_lib::task::TaskInfo */
typedef TaskInfo {
	mtype state = Ready;
	byte scheduler_type;// The lower the value, the higher the priority.
	bool need_sched = false;
	byte id;// This also represents the priority of the task. The lower the value,the higher the priority.
	bool need_preemption = false;
	short thread = - 1;// tid when this task is preempted, -1 otherwise.
}

TaskInfo tasks[TASK_NUM]

short RUNNING[CPU_NUM] = - 1// task_id when this CPU is executing a task, -1 otherwise.
bool interrupt_enabled[CPU_NUM] = false// Whether the interrupt handler is enabled in each CPU.
chan ipi_requests[CPU_NUM] = [TASK_NUM] of { byte }// task_id that requested preemption.
short NEXT_TASK[CPU_NUM] = - 1// Although this is a vector in Awkernel, this model addresses these like atomic variables.
chan PREEMPTED_TASK[CPU_NUM] = [TASK_NUM] of { byte }// Preempted task_id.

/* Scheduler queues */ 
chan queue[SCHEDULER_TYPE_NUM] = [TASK_NUM] of { byte }// task_ids in ascending order of priority.

#define cpu_id(tid) workers[tid].executing_in

#include "mutex.pml"
Mutex lock_info[TASK_NUM]
Mutex lock_queue[SCHEDULER_TYPE_NUM]

#define BYTE_MAX 255
