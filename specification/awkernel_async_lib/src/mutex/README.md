## How to run

1. download tla2tools

Download from here: https://github.com/tlaplus/tlaplus/releases

2. Translate PlusCal to TLA+
```bash
java -cp tla2tools.jar pcal.trans mutex.tla
```

1. Run TLC
```bash
java -jar tla2tools.jar -deadlock -config mutex.cfg mutex.tla
```


## Result

### starvation free model

```txt
$ java -jar tla2tools.jar -deadlock -config mutex.cfg mutex.tla
TLC2 Version 2.20 of Day Month 20?? (rev: cc65eef)
Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 85 and seed -7431744919228688868 with 1 worker on 22 cores with 7968MB heap and 64MB offheap memory [pid: 6275] (Linux 6.8.0-47-generic amd64, Ubuntu 11.0.24 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/mutex.tla
Warning: symbols were renamed.
Parsing file /tmp/tlc-4117199622809487545/TLC.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/tlc-4117199622809487545/Integers.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/tlc-4117199622809487545/Sequences.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/tlc-4117199622809487545/_TLCTrace.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/tlc-4117199622809487545/Naturals.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/tlc-4117199622809487545/FiniteSets.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Parsing file /tmp/tlc-4117199622809487545/TLCExt.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module Integers
Semantic processing of module TLCExt
Semantic processing of module _TLCTrace
Semantic processing of module mutex
Starting... (2024-10-28 08:43:07)
Implied-temporal checking--satisfiability problem has 1 branches.
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2024-10-28 08:43:07.
Progress(19) at 2024-10-28 08:43:07: 205 states generated, 133 distinct states found, 0 states left on queue.
Checking temporal properties for the complete state space with 133 total distinct states at (2024-10-28 08:43:07)
Finished checking temporal properties in 00s at 2024-10-28 08:43:07
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 5.2E-16
205 states generated, 133 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 19.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 2 and the 95th percentile is 2).
Finished in 00s at (2024-10-28 08:43:07)
```

### starvation model

Try after `check_again` block is removed.

```txt
$ java -jar tla2tools.jar -deadlock -config mutex.cfg mutex.tla
TLC2 Version 2.20 of Day Month 20?? (rev: cc65eef)
Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 113 and seed -7560130060587069646 with 1 worker on 22 cores with 7968MB heap and 64MB offheap memory [pid: 6437] (Linux 6.8.0-47-generic amd64, Ubuntu 11.0.24 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/mutex.tla
Warning: symbols were renamed.
Parsing file /tmp/tlc-10283909552580610438/TLC.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/tlc-10283909552580610438/Integers.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/tlc-10283909552580610438/Sequences.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/tlc-10283909552580610438/_TLCTrace.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/tlc-10283909552580610438/Naturals.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/tlc-10283909552580610438/FiniteSets.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Parsing file /tmp/tlc-10283909552580610438/TLCExt.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module Integers
Semantic processing of module TLCExt
Semantic processing of module _TLCTrace
Semantic processing of module mutex
Starting... (2024-10-28 08:44:25)
Implied-temporal checking--satisfiability problem has 1 branches.
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2024-10-28 08:44:25.
Progress(18) at 2024-10-28 08:44:25: 109 states generated, 77 distinct states found, 0 states left on queue.
Checking temporal properties for the complete state space with 77 total distinct states at (2024-10-28 08:44:25)
Error: Temporal properties were violated.

Error: The following behavior constitutes a counter-example:

State 1: <Initial predicate>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<>>, <<>>>>
/\ waiting = FALSE
/\ lock_var = FALSE
/\ pc = <<"start_thread", "start_thread">>
/\ data = 0
/\ thread = <<defaultInitValue, defaultInitValue>>

State 2: <start_thread(2) line 142, col 23 to line 149, col 79 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<>>, <<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>>>
/\ waiting = FALSE
/\ lock_var = FALSE
/\ pc = <<"start_thread", "start_lock">>
/\ data = 0
/\ thread = <<defaultInitValue, defaultInitValue>>

State 3: <start_lock(2) line 94, col 21 to line 102, col 67 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<>>, <<>>>>
/\ waiting = FALSE
/\ lock_var = TRUE
/\ pc = <<"start_thread", "add_data">>
/\ data = 0
/\ thread = <<defaultInitValue, defaultInitValue>>

State 4: <start_thread(1) line 142, col 23 to line 149, col 79 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>, <<>>>>
/\ waiting = FALSE
/\ lock_var = TRUE
/\ pc = <<"start_lock", "add_data">>
/\ data = 0
/\ thread = <<defaultInitValue, defaultInitValue>>

State 5: <start_lock(1) line 94, col 21 to line 102, col 67 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>, <<>>>>
/\ waiting = FALSE
/\ lock_var = TRUE
/\ pc = <<"enqueue_thread", "add_data">>
/\ data = 0
/\ thread = <<defaultInitValue, defaultInitValue>>

State 6: <add_data(2) line 151, col 19 to line 155, col 43 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>, <<>>>>
/\ waiting = FALSE
/\ lock_var = TRUE
/\ pc = <<"enqueue_thread", "end_thread">>
/\ data = 1
/\ thread = <<defaultInitValue, defaultInitValue>>

State 7: <end_thread(2) line 157, col 21 to line 164, col 79 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>, <<[pc |-> "Done", thread |-> defaultInitValue, procedure |-> "unlock"]>>>>
/\ waiting = FALSE
/\ lock_var = TRUE
/\ pc = <<"enqueue_thread", "start_unlock">>
/\ data = 1
/\ thread = <<defaultInitValue, defaultInitValue>>

State 8: <start_unlock(2) line 119, col 23 to line 125, col 47 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>, <<[pc |-> "Done", thread |-> defaultInitValue, procedure |-> "unlock"]>>>>
/\ waiting = FALSE
/\ lock_var = FALSE
/\ pc = <<"enqueue_thread", "wake">>
/\ data = 1
/\ thread = <<defaultInitValue, defaultInitValue>>

State 9: <wake(2) line 127, col 15 to line 132, col 39 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>, <<[pc |-> "Done", thread |-> defaultInitValue, procedure |-> "unlock"]>>>>
/\ waiting = FALSE
/\ lock_var = FALSE
/\ pc = <<"enqueue_thread", "Error">>
/\ data = 1
/\ thread = <<defaultInitValue, defaultInitValue>>

State 10: <enqueue_thread(1) line 104, col 25 to line 108, col 49 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>, <<[pc |-> "Done", thread |-> defaultInitValue, procedure |-> "unlock"]>>>>
/\ waiting = TRUE
/\ lock_var = FALSE
/\ pc = <<"poll_lock", "Error">>
/\ data = 1
/\ thread = <<defaultInitValue, defaultInitValue>>

State 11: Stuttering
Finished checking temporal properties in 00s at 2024-10-28 08:44:26
109 states generated, 77 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 18.
Finished in 00s at (2024-10-28 08:44:26)
Trace exploration spec path: ./mutex_TTrace_1730072665.tla
```