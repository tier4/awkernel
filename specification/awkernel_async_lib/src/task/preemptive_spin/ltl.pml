ltl ensure_priority {
	[] ((
			!waking[0] && !waking[1] && !waking[2] && !waking[3] && 
			len(ipi_requests[0]) == 0 && len(ipi_requests[1]) == 0 &&
			!workers[0].interrupted && !workers[1].interrupted && !workers[2].interrupted && !workers[3].interrupted &&
			RUNNING[0] != -1 && RUNNING[1] != -1
		) -> (running_lowest_priority < runnable_preempted_highest_priority))
}
