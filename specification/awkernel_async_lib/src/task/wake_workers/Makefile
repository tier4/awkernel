pan.c: wake_workers.pml
	spin -a $<

pan: pan.c
	gcc -O3 -o -DVECTORSZ=5000 $@ $<

run: pan
	rm -f *.trail
	./pan -a -n -m30000

trail:
	spin -plgrc -t wake_workers.pml

clean:
	rm -f pan.* *.trail pan *.tmp
