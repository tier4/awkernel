ltl eventually_prerequisites {
	[]<>
	(waking[0] == 0 && waking[1] == 0 && waking[2] == 0 && waking[3] == 0 &&
	len(ipi_requests[0]) == 0 && len(ipi_requests[1]) == 0 && 
	!handling_interrupt[0] && !handling_interrupt[1] && !handling_interrupt[2] && !handling_interrupt[3])
}

ltl ensure_priority {
	[]
	((waking[0] == 0 && waking[1] == 0 && waking[2] == 0 && waking[3] == 0 &&
	len(ipi_requests[0]) == 0 && RUNNING[0] != - 1 && RUNNING[0] != runnable_preempted_highest_priority && 
	len(ipi_requests[1]) == 0 && RUNNING[1] != - 1 && RUNNING[1] != runnable_preempted_highest_priority && 
	!handling_interrupt[0] && !handling_interrupt[1] && !handling_interrupt[2] && !handling_interrupt[3])
	-> (running_lowest_priority < runnable_preempted_highest_priority))
}
