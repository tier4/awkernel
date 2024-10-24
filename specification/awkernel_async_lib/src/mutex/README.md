## How to run

1. download tla2tools

2. Translate PlusCal to TLA+
```bash
java -cp tla2tools.jar pcal.trans mutex.tla
```

3. Run TLC
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
Running breadth-first search Model-Checking with fp 96 and seed 6478384794873034978 with 1 worker on 22 cores with 7968MB heap and 64MB offheap memory [pid: 122953] (Linux 6.8.0-47-generic amd64, Ubuntu 11.0.24 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/mutex.tla
Warning: symbols were renamed.
Parsing file /tmp/tlc-3295666740157571331/TLC.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/tlc-3295666740157571331/Integers.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/tlc-3295666740157571331/Sequences.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/tlc-3295666740157571331/_TLCTrace.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/tlc-3295666740157571331/Naturals.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/tlc-3295666740157571331/FiniteSets.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Parsing file /tmp/tlc-3295666740157571331/TLCExt.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module Integers
Semantic processing of module TLCExt
Semantic processing of module _TLCTrace
Semantic processing of module mutex
Starting... (2024-10-24 18:57:15)
Implied-temporal checking--satisfiability problem has 1 branches.
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2024-10-24 18:57:15.
Progress(17) at 2024-10-24 18:57:15: 157 states generated, 104 distinct states found, 0 states left on queue.
Checking temporal properties for the complete state space with 104 total distinct states at (2024-10-24 18:57:15)
Finished checking temporal properties in 00s at 2024-10-24 18:57:15
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 3.0E-16
157 states generated, 104 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 17.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 2 and the 95th percentile is 2).
Finished in 00s at (2024-10-24 18:57:15)
```

### starvation model

Try after `check_again` block is removed.

```txt
$ java -jar tla2tools.jar -deadlock -config mutex.cfg mutex.tla
TLC2 Version 2.20 of Day Month 20?? (rev: cc65eef)
Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 32 and seed -7046157286598512618 with 1 worker on 22 cores with 7968MB heap and 64MB offheap memory [pid: 121864] (Linux 6.8.0-47-generic amd64, Ubuntu 11.0.24 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/mutex.tla
Warning: symbols were renamed.
Parsing file /tmp/tlc-5687866999298315517/TLC.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/tlc-5687866999298315517/Integers.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/tlc-5687866999298315517/Sequences.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/tlc-5687866999298315517/_TLCTrace.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/tlc-5687866999298315517/Naturals.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/tlc-5687866999298315517/FiniteSets.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Parsing file /tmp/tlc-5687866999298315517/TLCExt.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module Integers
Semantic processing of module TLCExt
Semantic processing of module _TLCTrace
Semantic processing of module mutex
Starting... (2024-10-24 18:41:30)
Implied-temporal checking--satisfiability problem has 1 branches.
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2024-10-24 18:41:30.
Progress(16) at 2024-10-24 18:41:30: 105 states generated, 73 distinct states found, 0 states left on queue.
Checking temporal properties for the complete state space with 73 total distinct states at (2024-10-24 18:41:30)
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

State 2: <start_thread(1) line 134, col 23 to line 141, col 79 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>, <<>>>>
/\ waiting = FALSE
/\ lock_var = FALSE
/\ pc = <<"start_lock", "start_thread">>
/\ data = 0
/\ thread = <<defaultInitValue, defaultInitValue>>

State 3: <start_lock(1) line 91, col 21 to line 99, col 67 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<>>, <<>>>>
/\ waiting = FALSE
/\ lock_var = TRUE
/\ pc = <<"add_data", "start_thread">>
/\ data = 0
/\ thread = <<defaultInitValue, defaultInitValue>>

State 4: <add_data(1) line 143, col 19 to line 147, col 43 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<>>, <<>>>>
/\ waiting = FALSE
/\ lock_var = TRUE
/\ pc = <<"end_thread", "start_thread">>
/\ data = 1
/\ thread = <<defaultInitValue, defaultInitValue>>

State 5: <start_thread(2) line 134, col 23 to line 141, col 79 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<>>, <<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>>>
/\ waiting = FALSE
/\ lock_var = TRUE
/\ pc = <<"end_thread", "start_lock">>
/\ data = 1
/\ thread = <<defaultInitValue, defaultInitValue>>

State 6: <end_thread(1) line 149, col 21 to line 156, col 79 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "Done", thread |-> defaultInitValue, procedure |-> "unlock"]>>, <<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>>>
/\ waiting = FALSE
/\ lock_var = TRUE
/\ pc = <<"start_unlock", "start_lock">>
/\ data = 1
/\ thread = <<defaultInitValue, defaultInitValue>>

State 7: <start_lock(2) line 91, col 21 to line 99, col 67 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "Done", thread |-> defaultInitValue, procedure |-> "unlock"]>>, <<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>>>
/\ waiting = FALSE
/\ lock_var = TRUE
/\ pc = <<"start_unlock", "enqueue_thread">>
/\ data = 1
/\ thread = <<defaultInitValue, defaultInitValue>>

State 8: <start_unlock(1) line 116, col 23 to line 122, col 47 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "Done", thread |-> defaultInitValue, procedure |-> "unlock"]>>, <<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>>>
/\ waiting = FALSE
/\ lock_var = FALSE
/\ pc = <<"wake", "enqueue_thread">>
/\ data = 1
/\ thread = <<defaultInitValue, defaultInitValue>>

State 9: <wake(1) line 124, col 15 to line 130, col 81 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "Done", thread |-> defaultInitValue, procedure |-> "unlock"]>>, <<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>>>
/\ waiting = FALSE
/\ lock_var = FALSE
/\ pc = <<"Error", "enqueue_thread">>
/\ data = 1
/\ thread = <<defaultInitValue, defaultInitValue>>

State 10: <enqueue_thread(2) line 101, col 25 to line 105, col 49 of module mutex>
/\ waken = FALSE
/\ thread_l = <<defaultInitValue, defaultInitValue>>
/\ stack = <<<<[pc |-> "Done", thread |-> defaultInitValue, procedure |-> "unlock"]>>, <<[pc |-> "add_data", thread_l |-> defaultInitValue, procedure |-> "lock"]>>>>
/\ waiting = TRUE
/\ lock_var = FALSE
/\ pc = <<"Error", "poll_lock">>
/\ data = 1
/\ thread = <<defaultInitValue, defaultInitValue>>

State 11: Stuttering
Finished checking temporal properties in 00s at 2024-10-24 18:41:30
105 states generated, 73 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 16.
Finished in 00s at (2024-10-24 18:41:30)
Trace exploration spec path: ./mutex_TTrace_1729762889.tla
```