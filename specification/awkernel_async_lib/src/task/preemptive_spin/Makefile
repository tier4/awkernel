pan.c: preemptive.pml
	spin -a $<

pan: pan.c
	gcc -O3 -DVECTORSZ=10000 -DNFAIR=3 -o $@ $<

run: pan
	rm -f *.trail
	./pan -f -a -n

trail:
	spin -plgrc -t preemptive.pml

clean:
	rm -f pan.* *.trail pan *.tmp
