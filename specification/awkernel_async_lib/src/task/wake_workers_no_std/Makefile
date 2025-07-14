# $(TARGET):
#   EVENTUALLY_EXECUTE
#   CPU_WAKING_TO_ACTIVE

# $(TIMER):
#   TIMER_EDGE

# $(IRQ_POS):
#   0, 1, 2, or 3

pan.c: wake_workers.pml
	spin -a -D$(TARGET) -D$(TIMER) -DIRQ_POS=$(IRQ_POS) $<

pan: pan.c
	gcc -O3 -DCOLLAPSE -DMEMLIM=57344 -o $@ $<

run: pan
	rm -f *.trail
	./pan -a -n

trail:
	spin -D$(TARGET) -D$(TIMER) -DIRQ_POS=$(IRQ_POS) -plgrc -t wake_workers.pml

clean:
	rm -f pan.* *.trail pan *.tmp
