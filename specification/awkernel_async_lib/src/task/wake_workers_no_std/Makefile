# $(TARGET):
#   EVENTUALLY_EXECUTE
#   CPU_WAKING_TO_ACTIVE

pan.c: wake_workers.pml
	spin -a -D$(TARGET) $<

pan: pan.c
	gcc -O3 -DCOLLAPSE -o $@ $<

run: pan
	rm -f *.trail
	./pan -a -n

trail:
	spin -plgrc -t wake_workers.pml

clean:
	rm -f pan.* *.trail pan *.tmp
