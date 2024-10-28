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

```txt
$ java -jar tla2tools.jar -deadlock -config mutex.cfg mutex.tla
TLC2 Version 2.20 of Day Month 20?? (rev: cc65eef)
Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
(Use the -nowarning option to disable this warning.)
Running breadth-first search Model-Checking with fp 8 and seed 9005314221143410698 with 1 worker on 22 cores with 7968MB heap and 64MB offheap memory [pid: 286760] (Linux 6.8.0-47-generic amd64, Ubuntu 11.0.24 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/mutex.tla
Warning: symbols were renamed.
Parsing file /tmp/tlc-17980086720064727317/TLC.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/tlc-17980086720064727317/Integers.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/tlc-17980086720064727317/Sequences.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/tlc-17980086720064727317/_TLCTrace.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/tlc-17980086720064727317/Naturals.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/tlc-17980086720064727317/FiniteSets.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Parsing file /tmp/tlc-17980086720064727317/TLCExt.tla (jar:file:/home/veqcc/work/awkernel/specification/awkernel_async_lib/src/mutex/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module Integers
Semantic processing of module TLCExt
Semantic processing of module _TLCTrace
Semantic processing of module mutex
Starting... (2024-10-28 10:55:08)
Implied-temporal checking--satisfiability problem has 1 branches.
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2024-10-28 10:55:08.
Progress(13) at 2024-10-28 10:55:08: 85 states generated, 50 distinct states found, 0 states left on queue.
Checking temporal properties for the complete state space with 50 total distinct states at (2024-10-28 10:55:08)
Finished checking temporal properties in 00s at 2024-10-28 10:55:08
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 9.5E-17
85 states generated, 50 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 13.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 2 and the 95th percentile is 2).
Finished in 00s at (2024-10-28 10:55:08)
```
