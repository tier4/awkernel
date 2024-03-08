# Cooperative Multitasking

See [specification/awkernel_async_lib/src/tasl/cooperative/](../cooperative/) first, since the model is based on it.
The difference is that some tasks are supposed to include an infinite loop so that we can specify the following property.

## Targets

- [awkernel_async_lib/src/task.rs](../../../../../awkernel_async_lib/src/task.rs).
- [awkernel_async_lib/src/scheduler/fifo.rs](../../../../../awkernel_async_lib/src/scheduler/fifo.rs).

## Subjects to be Verified

1. When tasks are more than workers, all tasks will be eventually executes.

## Result

```
TLC2 Version 2.18 of 20 March 2023 (rev: 3ea3222)
Running breadth-first search Model-Checking with fp 110 and seed 3903929992870451646 with 16 workers on 16 cores with 14160MB heap and 64MB offheap memory [pid: 44994] (Linux 6.5.0-21-generic amd64, Private Build 19.0.2 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /home/ytakano/program/rust/awkernel/specification/awkernel_async_lib/src/task/cooperative_with_infinite_loop/cooperative_with_infinite_loop.tla
Warning: symbols were renamed.
Parsing file /tmp/TLC.tla
Parsing file /tmp/Integers.tla
Parsing file /tmp/Sequences.tla
Parsing file /tmp/Naturals.tla
Parsing file /tmp/FiniteSets.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module Integers
Semantic processing of module cooperative_with_infinite_loop
Starting... (2024-03-08 09:31:02)
Implied-temporal checking--satisfiability problem has 1 branches.
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2024-03-08 09:31:02.
Progress(209) at 2024-03-08 09:31:04: 169,349 states generated, 85,845 distinct states found, 0 states left on queue.
Checking temporal properties for the complete state space with 85845 total distinct states at (2024-03-08 09:31:04)
Finished checking temporal properties in 29min 49s at 2024-03-08 10:00:53
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 3.9E-10
  based on the actual fingerprints:  val = 1.4E-9
169349 states generated, 85845 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 209.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 2 and the 95th percentile is 2).
Finished in 29min 52s at (2024-03-08 10:00:53)
```
