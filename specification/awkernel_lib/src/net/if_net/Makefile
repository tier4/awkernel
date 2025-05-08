pan.c: if_net.pml
	spin -a $<

pan: pan.c
	gcc -O3 -o $@ $<

run: pan
	rm -f *.trail
	./pan -a -n

trail:
	spin -plgrc -t if_net.pml

clean:
	rm -f pan.* *.trail pan *.tmp
