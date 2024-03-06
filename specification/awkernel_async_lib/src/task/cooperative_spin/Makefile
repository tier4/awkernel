pan.c: cooperative.pml
	spin -a $<

pan: pan.c
	gcc -O3 -o $@ $<

run: pan
	./pan -f -a -m1000000000

pan_bfs: pan.c
	gcc -O3 -DBFS -o $@ $<

run_bfs: pan_bfs
	./pan_bfs -m100000000

trail:
	spin -plgrc -t cooperative.pml

clean:
	rm -f pan.* *.trail pan pan_bfs
