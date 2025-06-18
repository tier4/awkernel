pan.c: preemptive.pml
	spin -a $<

pan: pan.c
	gcc -O3 -DVECTORSZ=5000 -DNFAIR=3 -o $@ $<

run: pan
	rm -f *.trail
	./pan -f -a -n -m30000

trail:
	clear
	spin -t -p preemptive.pml

clean:
	rm -f pan.* *.trail pan *.tmp
