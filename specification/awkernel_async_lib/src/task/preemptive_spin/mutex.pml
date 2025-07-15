typedef Mutex {
	bool is_locked = false;
	bool interrupt_flag[WORKER_NUM];// This stores the interrupt enabled state of each CPU when the lock is acquired.
}

inline lock(tid,mutex) {
	d_step {
		if
		:: cpu_id(tid) != - 1 -> 
			mutex.interrupt_flag[tid] = interrupt_enabled[cpu_id(tid)];
			interrupt_enabled[cpu_id(tid)] = false;
		:: else
		fi
	}
	
	atomic {!mutex.is_locked -> mutex.is_locked = true}
}

inline unlock(tid,mutex) {
	mutex.is_locked = false;

	d_step {
		if
		:: cpu_id(tid) != - 1 -> 
			interrupt_enabled[cpu_id(tid)] = mutex.interrupt_flag[tid];
			mutex.interrupt_flag[tid] = false
		:: else
		fi;
	}
}
