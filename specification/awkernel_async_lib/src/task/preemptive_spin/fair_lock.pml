#define NUM_PROC WORKER_NUM

typedef FairLock {
	bool is_locked;
	bool flag[NUM_PROC];
	chan request = [NUM_PROC - 1] of { int };
	bool interrupt_flag[NUM_PROC];// This stores the interrupt enabled state of each CPU when the lock is acquired.
};

inline lock(tid,mutex) {
	atomic {
		if
		:: cpu_id(tid) != - 1 -> 
			mutex.interrupt_flag[tid] = interrupt_enabled[cpu_id(tid)];
			interrupt_enabled[cpu_id(tid)] = false;
		:: else
		fi
	}
	
	bool need_wait = false;
	if
	:: atomic {
			mutex.is_locked -> 
			assert(!mutex.request?[tid]);// Deadlock
			mutex.flag[tid] = false;
			mutex.request!tid;
			need_wait = true;
		}
	:: atomic {
			!mutex.is_locked -> 
			mutex.is_locked = true;
		}
	fi;
	
	if
	:: need_wait -> 
		mutex.flag[tid];
	:: else
	fi
}

inline unlock(tid,mutex) {
	atomic {
		int p;
		if
		:: mutex.request?[p] -> 
			mutex.request?p;
			mutex.flag[p] = true;
		:: else -> 
			mutex.is_locked = false;
		fi;
	}
	
	atomic {
		if
		:: cpu_id(tid) != - 1 -> 
			interrupt_enabled[cpu_id(tid)] = mutex.interrupt_flag[tid];
			mutex.interrupt_flag[tid] = false;
		:: else
		fi;
	}
}
