ltl ensure_priority {
	[] ((
			!waking[0] && !waking[1] && !waking[2] && !waking[3] && 
			len(ipi_requests[0]) == 0 && len(ipi_requests[1]) == 0 &&
			!handling_interrupt[0] && !handling_interrupt[1] && !handling_interrupt[2] && !handling_interrupt[3] &&
			RUNNING[0] != -1 && RUNNING[1] != -1
		) -> (running_lowest_priority < runnable_preempted_highest_priority))
}
