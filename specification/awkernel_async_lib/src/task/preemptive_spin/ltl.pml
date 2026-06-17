ltl eventually_terminate {
	<> (num_terminated == TASK_NUM)
}

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

ltl killed_task_eventually_terminated_and_not_running {
	[](
	(!killed[0] || (<>(tasks[0].state == Terminated && RUNNING[0] != 0 && RUNNING[1] != 0)) ) &&
	(!killed[1] || (<>(tasks[1].state == Terminated && RUNNING[0] != 1 && RUNNING[1] != 1)) ) &&
	(!killed[2] || (<>(tasks[2].state == Terminated && RUNNING[0] != 2 && RUNNING[1] != 2)) ) &&
	(!killed[3] || (<>(tasks[3].state == Terminated && RUNNING[0] != 3 && RUNNING[1] != 3)) )
	)
}

ltl kill_pending_eventually_terminated {
	[]((!tasks[0].kill_pending || <> (tasks[0].state == Terminated)) &&
	   (!tasks[1].kill_pending || <> (tasks[1].state == Terminated)) &&
	   (!tasks[2].kill_pending || <> (tasks[2].state == Terminated)) &&
	   (!tasks[3].kill_pending || <> (tasks[3].state == Terminated)))
}
