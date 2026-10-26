//! One module per DAG admission policy: an algorithm that turns
//! [`super::metrics::DagMetrics`] (and, where needed, [`super::graph::DagGraph`])
//! into an admission decision and a [`crate::scheduler::SchedulerType`] for a
//! DAG's nodes.

pub mod dag_fluid;
pub mod federated;
pub mod sfs;
pub mod vfed;
