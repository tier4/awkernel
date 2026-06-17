pan.c: preemptive.pml
	spin -a $<

pan: pan.c
	gcc -O3 -DCOLLAPSE -DVECTORSZ=5000 -DNFAIR=3 -o $@ $<

run: pan
	rm -f *.trail
	./pan -a -n -m30000

kill-test:
	rm -f pan pan.* *.trail *.tmp _spin_nvr.tmp kill-test-*.log
	spin -a -DKILL_TEST preemptive.pml
	gcc -O3 -DCOLLAPSE -DVECTORSZ=5000 -DNFAIR=3 -o pan pan.c
	./pan -a -n -m30000 -N killed_task_eventually_terminated_and_not_running | tee kill-test-killed.log
	grep -q "errors: 0" kill-test-killed.log
	./pan -a -n -m30000 -N kill_pending_eventually_terminated | tee kill-test-pending.log
	grep -q "errors: 0" kill-test-pending.log

trail:
	clear
	spin -t preemptive.pml

clean:
	rm -f pan.* *.trail pan *.tmp _spin_nvr.tmp kill-test-*.log
