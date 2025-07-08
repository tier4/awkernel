# $(TARGET):
#   EVENTUALLY_EXECUTE
#   CPU_WAKING_TO_ACTIVE

# $(TIMER):
#   TIMER_EDGE

pan.c: wake_workers.pml
	spin -a -D$(TARGET) -D$(TIMER) $<

pan: pan.c
	gcc -O3 -DCOLLAPSE -o $@ $<

run: pan
	rm -f *.trail
	./pan -a -n

trail:
	spin -plgrc -t wake_workers.pml

clean:
	rm -f pan.* *.trail pan *.tmp
