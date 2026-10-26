//! DAG scheduling *policy* layer: decides which [`crate::scheduler::SchedulerType`]
//! and which cores a DAG's nodes should use. A sibling of [`crate::dag`]
//! (graph structure) and [`crate::scheduler`] (run-queue mechanisms) rather
//! than a child of either, so that adding an admission algorithm never
//! requires touching the run queues, and adding a run queue never requires
//! knowing which admission algorithm feeds it.
//!
//! Split into layers so each concern is isolated from the others:
//!
//! - [`metrics`]: the DAG-level numbers every admission policy reads
//!   ([`metrics::DagMetrics`]) and how they were obtained
//!   ([`metrics::MetricsSource`]).
//! - [`resource`]: the shared, algorithm-agnostic ledger of which cores are
//!   claimed and how much of the shared pool's utilization is committed.
//! - [`precondition`]: each policy's preconditions on a DAG's timing as one
//!   table, checked into a [`crate::dag::DagError`] before admission.
//! - [`admission`]: [`admission::AdmissionError`], the one error type every
//!   policy's admission returns.
//! - [`graph`]: [`graph::DagGraph`], a DAG's precedence structure (node
//!   WCETs and edges) as the structure-aware admission tests read it.
//! - [`policy`]: one module per admission algorithm (Federated, V-Fed,
//!   SFS, DAG-Fluid), each combining `metrics`/`graph`/`resource` into that
//!   algorithm's own admission test and turning its decision into a
//!   [`crate::scheduler::SchedulerType`].
//! - [`dp_partition`]: system-wide Deadline-Partition boundary tracking for
//!   DAG-Fluid's dynamic-dispatch measurement work (Phase 2) — a
//!   measurement probe, not a scheduling mechanism; see its own module doc.
pub mod admission;
pub mod dp_partition;
pub mod graph;
pub mod metrics;
pub mod partition;
pub mod policy;
pub mod precondition;
pub mod resource;
