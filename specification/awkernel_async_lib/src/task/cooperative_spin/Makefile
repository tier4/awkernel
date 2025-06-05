pan.c: cooperative.pml
	spin -a $<

pan: pan.c
	gcc -O3 -o $@ $<

run: pan
	rm -f *.trail
	./pan -f -a -n

trail:
	spin -plgrc -t cooperative.pml

clean:
	rm -f pan.* *.trail pan *.tmp
