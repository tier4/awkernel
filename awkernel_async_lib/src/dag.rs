//! Provides functionality for building and executing Directed Acyclic Graphs (DAGs) of reactors.
//!
//! # Main Workflow
//!
//! 1. Create a new `Dag` instance by calling the `create_dag` function.
//! 2. Define the graph structure by calling methods on the `Dag` instance (e.g., `register_reactor`) to register reactors as nodes.
//! 3. Once all DAGs are defined, call the `finish_create_dags` function.
//!    This validates the DAGs and spawns all registered reactor tasks, starting their execution.
//!
//! # Key Public Components
//!
//! - `Dag`: The central struct representing an individual task graph.
//! - `create_dag()`: The entry point for creating a new DAG.
//! - `register_xx_reactor()`: Methods to register different types of reactors.
//! - `finish_create_dags()`: The function to validate the defined DAGs and start their execution.
//! - `DagError`: Defines potential errors that can occur during DAG validation.
//!
//! # DAG Constraints and Validation
//!
//! To ensure data flow integrity and predictable execution, the system enforces several constraints during the `finish_create_dags` call.
//!
//! ## 1. Structural Integrity
//! These rules concern the overall shape of the graph.
//!
//! - **Must be Acyclic**: The graph cannot contain any directed cycles.
//! - **Must be Connected**: All nodes must form a single, weakly connected component. Orphaned nodes or subgraphs are not allowed.
//!
//! ## 2. Register API Interface Correctness
//!
//! - **Arity Matching**: The number of topics a reactor subscribes to must match its function's argument count. The number of topics it publishes must match its return value count.
//! - **No Duplicate Subscriptions/Publications**: A single reactor cannot subscribe to or publish the same topic multiple times.
//!
//! ## 3. Data Flow Integrity
//!
//! - **No Dangling Edges**: Every published topic must be subscribed to by another node, and every subscribed topic must have a publisher.
//! - **Globally Unique Topics (Inter-DAG)**: A topic name must be unique across all active DAGs in the system. This prevents different data pipelines from unintentionally interfering with each other.
//!
//! # Example Usage
//!
//! See the `applications/tests/test_dag` example for practical usage.
//!
//! # Notes
//!
//! This constraint may be relaxed in the future to support more complex topologies.
//!
//! - **Single Publisher per Topic (Intra-DAG)**: Within a single DAG, a topic can only be published to by one node.
//! - **Source and Sink**: The current implementation assumes that a DAG has a single source and a single sink.
//!
mod graph;
mod unionfind;
mod visit;

#[cfg(feature = "perf")]
mod performance;

use crate::{
    dag::{
        graph::{
            algo::{connected_components, is_cyclic_directed},
            direction::Direction,
            NodeIndex,
        },
        visit::{EdgeRef, IntoNodeReferences, NodeRef},
    },
    scheduler::SchedulerType,
    task::{DagInfo, State},
    time_interval::interval,
    Attribute, MultipleReceiver, MultipleSender, VectorToPublishers, VectorToSubscribers,
};

#[cfg(feature = "period-index-propagation")]
use crate::task::perf::{
    get_period_index, increment_period_index, record_subscribe_timestamp,
    update_cycle_end_timestamp, update_cycle_start_timestamp,
};

use alloc::{
    borrow::Cow,
    boxed::Box,
    collections::{btree_map, btree_set::BTreeSet, BTreeMap},
    string::String,
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::{future::Future, pin::Pin, time::Duration};

#[cfg(feature = "perf")]
use performance::ResponseInfo;

static DAGS: Mutex<Dags> = Mutex::new(Dags::new()); // Set of DAGs.

/// `(dag_id, reason)` for every DAG that got as far as `create_dag()` (so it
/// has a `dag_id`) but then failed to build -- e.g. rejected by admission
/// control, or a link-count/arity error -- and so was never spawned and
/// never appears in `TRACE_TASK`. Recorded independently of the trace
/// window (see `task::trace`'s `start`/`stop`) because DAG building
/// typically finishes before auto-trace's start delay elapses; read out by
/// `task::trace::dump_to_console`, which turns each entry into a
/// `TRACE_BUILD_MISS` line so host-side tooling (`plot_trace.py`) can count
/// it as a miss alongside runtime deadline misses instead of it silently
/// vanishing.
static BUILD_FAILURES: Mutex<Vec<(u32, String)>> = Mutex::new(Vec::new());

/// Record that `dag_id` failed to build and will therefore never run. See
/// `BUILD_FAILURES`.
pub fn record_build_failure(dag_id: u32, reason: String) {
    let mut node = MCSNode::new();
    let mut failures = BUILD_FAILURES.lock(&mut node);
    failures.push((dag_id, reason));
}

/// Drain and return every build failure recorded so far via
/// `record_build_failure`. Used by `task::trace::dump_to_console`.
pub fn take_build_failures() -> Vec<(u32, String)> {
    let mut node = MCSNode::new();
    let mut failures = BUILD_FAILURES.lock(&mut node);
    core::mem::take(&mut *failures)
}

// The following BTreeMaps use dag_id (u32) as the key.
static PENDING_TASKS: Mutex<BTreeMap<u32, Vec<PendingTask>>> = Mutex::new(BTreeMap::new());
static SOURCE_PENDING_TASKS: Mutex<BTreeMap<u32, PendingTask>> = Mutex::new(BTreeMap::new());
static MISMATCH_SUBSCRIBE_NODES: Mutex<BTreeMap<u32, Vec<usize>>> = Mutex::new(BTreeMap::new());
static MISMATCH_PUBLISH_NODES: Mutex<BTreeMap<u32, Vec<usize>>> = Mutex::new(BTreeMap::new());
static DUPLICATE_SUBSCRIBE_NODES: Mutex<BTreeMap<u32, Vec<usize>>> = Mutex::new(BTreeMap::new());
static DUPLICATE_PUBLISH_NODES: Mutex<BTreeMap<u32, Vec<usize>>> = Mutex::new(BTreeMap::new());

type MeasureF = Arc<dyn Fn() + Send + Sync + 'static>;

pub trait TupleSize {
    const SIZE: usize;
}

macro_rules! impl_tuple_size {
    (@count) => { 0 };
    (@count $_head:ident $($tail:ident)*) => { 1 + impl_tuple_size!(@count $($tail)*) };

    ($($T:ident),*) => {
        impl<$($T),*> TupleSize for ($($T,)*) {
            const SIZE: usize = impl_tuple_size!(@count $($T)*);
        }
    };
}

impl_tuple_size!();
impl_tuple_size!(T1);
impl_tuple_size!(T1, T2);
impl_tuple_size!(T1, T2, T3);
impl_tuple_size!(T1, T2, T3, T4);
impl_tuple_size!(T1, T2, T3, T4, T5);
impl_tuple_size!(T1, T2, T3, T4, T5, T6);
impl_tuple_size!(T1, T2, T3, T4, T5, T6, T7);
impl_tuple_size!(T1, T2, T3, T4, T5, T6, T7, T8);
impl_tuple_size!(T1, T2, T3, T4, T5, T6, T7, T8, T9);
impl_tuple_size!(T1, T2, T3, T4, T5, T6, T7, T8, T9, T10);
impl_tuple_size!(T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11);
impl_tuple_size!(T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12);
impl_tuple_size!(T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13);
impl_tuple_size!(T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14);
impl_tuple_size!(T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15);
impl_tuple_size!(T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16);

/// Why a DAG cannot be created or admitted. The first group is structural
/// (checked when the DAG's nodes are registered); the second group is the
/// scheduling model's preconditions on the DAG's timing, checked per
/// admission policy through [`crate::dag_sched::precondition`] before any
/// admission test runs. Each carries the DAG's id -- or, when checked
/// before the DAGs are created (a batch admission), its position in the
/// batch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DagError {
    NotWeaklyConnected(u32),
    ContainsCycle(u32),
    MissingPendingTasks(u32),
    MultipleSourceNodes(u32),
    MultipleSinkNodes(u32),
    NoPublisherFound(u32, usize),
    NoSubscriberFound(u32, usize),
    SubscribeArityMismatch(u32, usize),
    PublishArityMismatch(u32, usize),
    DuplicateSubscribe(u32, usize),
    DuplicatePublish(u32, usize),
    TopicHasMultiplePublishers(u32, Cow<'static, str>),
    InterDagTopicConflict(Cow<'static, str>, Vec<u32>),

    /// The source node has no period or the sink node no end-to-end
    /// deadline, so the DAG has no timing to admit it by.
    MissingTiming(u32),
    /// `L > D`: traversing the critical path alone overruns the deadline,
    /// on any number of processors.
    CriticalPathExceedsDeadline {
        dag_id: u32,
        critical_path: u64,
        relative_deadline: u64,
    },
    /// `D == L` with `C > L`: the policy's processor count
    /// `ceil((C - L) / (D - L))` is undefined -- parallel-only work would
    /// have to fit in zero slack.
    NoSlackForParallelWork {
        dag_id: u32,
        volume: u64,
        critical_path: u64,
    },
    /// `D <= L`: the policy needs positive slack (`D - L > 0`) on every
    /// path.
    NonPositiveSlack {
        dag_id: u32,
        critical_path: u64,
        relative_deadline: u64,
    },
    /// `D != T`: the policy is defined for implicit deadlines only.
    ImplicitDeadlineRequired {
        dag_id: u32,
        relative_deadline: u64,
        period: u64,
    },
    /// `D > T`: the policy is defined for constrained deadlines only.
    ConstrainedDeadlineRequired {
        dag_id: u32,
        relative_deadline: u64,
        period: u64,
    },
}

impl DagError {
    /// The same error reported against `dag_id` -- for a precondition found
    /// by a per-DAG entry point that has no DAG id of its own (it reports
    /// 0). Structural errors, which always know their DAG, are unchanged.
    pub fn with_dag_id(self, dag_id: u32) -> Self {
        match self {
            DagError::MissingTiming(_) => DagError::MissingTiming(dag_id),
            DagError::CriticalPathExceedsDeadline {
                critical_path,
                relative_deadline,
                ..
            } => DagError::CriticalPathExceedsDeadline {
                dag_id,
                critical_path,
                relative_deadline,
            },
            DagError::NoSlackForParallelWork {
                volume,
                critical_path,
                ..
            } => DagError::NoSlackForParallelWork {
                dag_id,
                volume,
                critical_path,
            },
            DagError::NonPositiveSlack {
                critical_path,
                relative_deadline,
                ..
            } => DagError::NonPositiveSlack {
                dag_id,
                critical_path,
                relative_deadline,
            },
            DagError::ImplicitDeadlineRequired {
                relative_deadline,
                period,
                ..
            } => DagError::ImplicitDeadlineRequired {
                dag_id,
                relative_deadline,
                period,
            },
            DagError::ConstrainedDeadlineRequired {
                relative_deadline,
                period,
                ..
            } => DagError::ConstrainedDeadlineRequired {
                dag_id,
                relative_deadline,
                period,
            },
            other => other,
        }
    }
}

#[rustfmt::skip]
impl core::fmt::Display for DagError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DagError::NotWeaklyConnected(dag_id) => write!(f, "DAG#{dag_id} is not weakly connected"),
            DagError::ContainsCycle(dag_id) => write!(f, "DAG#{dag_id} contains a cycle"),
            DagError::MissingPendingTasks(dag_id) => write!(f, "DAG#{dag_id} has missing pending tasks"),
            DagError::MultipleSourceNodes(dag_id) => write!(f, "DAG#{dag_id} has multiple source nodes"),
            DagError::MultipleSinkNodes(dag_id) => write!(f, "DAG#{dag_id} has multiple sink nodes"),
            DagError::NoPublisherFound(dag_id, node_id) => {
                write!(f, "DAG#{dag_id} Node#{node_id}: One or more subscribed topics have no corresponding publisher")
            }
            DagError::NoSubscriberFound(dag_id, node_id) => {
                write!(f, "DAG#{dag_id} Node#{node_id}: One or more published topics have no corresponding subscriber")
            }
            DagError::SubscribeArityMismatch(dag_id, node_id) => {
                write!(f, "DAG#{dag_id} Node#{node_id}: Mismatch in subscribed topics and arguments")
            }
            DagError::PublishArityMismatch(dag_id, node_id) => {
                write!(f, "DAG#{dag_id} Node#{node_id}: Mismatch in published topics and return values")
            }
            DagError::DuplicateSubscribe(dag_id, node_id) => {
                write!(f, "DAG#{dag_id} Node#{node_id}: found duplicate subscription,")
            }
            DagError::DuplicatePublish(dag_id, node_id) => {
                write!(f, "DAG#{dag_id} Node#{node_id}: found duplicate publication.")
            }
            DagError::TopicHasMultiplePublishers(dag_id, topic_name) => {
                write!(f, "DAG#{dag_id}: Topic '{topic_name}' has multiple publishers")
            }
            DagError::InterDagTopicConflict(topic_name, dag_ids) => {
                write!(f, "Topic '{topic_name}' is used in multiple DAGs. Conflicting DAG IDs: {dag_ids:?}")
            }
            DagError::MissingTiming(dag_id) => {
                write!(f, "DAG#{dag_id} has no source period or no sink end-to-end deadline")
            }
            DagError::CriticalPathExceedsDeadline { dag_id, critical_path, relative_deadline } => {
                write!(f, "DAG#{dag_id}: critical_path({critical_path}) > relative_deadline({relative_deadline}); no processor count can meet it")
            }
            DagError::NoSlackForParallelWork { dag_id, volume, critical_path } => {
                write!(f, "DAG#{dag_id}: relative_deadline == critical_path({critical_path}) < volume({volume}); no slack for the parallel work")
            }
            DagError::NonPositiveSlack { dag_id, critical_path, relative_deadline } => {
                write!(f, "DAG#{dag_id}: relative_deadline({relative_deadline}) <= critical_path({critical_path}); this policy needs positive slack")
            }
            DagError::ImplicitDeadlineRequired { dag_id, relative_deadline, period } => {
                write!(f, "DAG#{dag_id}: relative_deadline({relative_deadline}) != period({period}); this policy needs implicit deadlines")
            }
            DagError::ConstrainedDeadlineRequired { dag_id, relative_deadline, period } => {
                write!(f, "DAG#{dag_id}: relative_deadline({relative_deadline}) > period({period}); this policy needs constrained deadlines")
            }
        }
    }
}

pub struct Dag {
    id: u32,
    graph: Mutex<graph::Graph<NodeInfo, EdgeInfo>>,

    /// Absolute deadline of each released job that a node has not finished, keyed by job number.
    /// A job is one run of the DAG. It starts when the source node wakes for a new release.
    absolute_deadlines: Mutex<BTreeMap<u64, u64>>,

    #[cfg(feature = "perf")]
    response_info: Mutex<ResponseInfo>,
}

impl Dag {
    pub fn get_id(&self) -> u32 {
        self.id
    }

    fn get_source_nodes(&self) -> Vec<NodeIndex> {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        graph.externals(Direction::Incoming).collect()
    }

    fn get_sink_nodes(&self) -> Vec<NodeIndex> {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        graph.externals(Direction::Outgoing).collect()
    }

    // Returns the relative deadline of the first sink node, if it exists.
    pub fn get_sink_relative_deadline(&self) -> Option<Duration> {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        let sink_node_index = graph.externals(Direction::Outgoing).next()?;
        graph.node_weight(sink_node_index)?.relative_deadline
    }

    fn set_relative_deadline(&self, node_idx: NodeIndex, deadline: Duration) {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        graph.node_weight_mut(node_idx).unwrap().relative_deadline = Some(deadline);
    }

    /// Set a scheduling-policy priority for node `node_id` (the same id
    /// carried on [`crate::task::DagInfo::node_id`], i.e. the registration
    /// order of `register_reactor`/`register_periodic_reactor`/
    /// `register_sink_reactor` for this DAG). `dag.rs` never interprets this
    /// value itself; it exists so a `dag_sched` policy (e.g. a laxity-based
    /// or other node-importance ranking, computed once the whole DAG's
    /// structure is known) can annotate individual nodes after registration.
    ///
    /// Silently does nothing if `node_id` does not name a node of this DAG.
    /// Call before [`finish_create_dags`], like [`Self::set_relative_deadline`]
    /// — nodes are already spawned and reading their `SchedulerType` by then.
    pub fn set_node_priority(&self, node_id: u32, priority: u64) {
        let node_idx = to_node_index(node_id);
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        if let Some(info) = graph.node_weight_mut(node_idx) {
            info.priority = Some(priority);
        }
    }

    /// The task id `node_id` was spawned as, or `None` if `node_id` does not
    /// name a node of this DAG. Used by `dag_sched::dp_partition` (DAG-Fluid
    /// real-machine dispatch) to check whether a specific node has actually
    /// finished (`task::get_task(id)`'s own `State::Terminated`), not just
    /// whether its *theoretical* segment deadline has passed — see that
    /// module's own doc for why the two can differ on real hardware.
    ///
    /// Uses [`Mutex::try_lock`] rather than a blocking `lock`: the caller
    /// runs from timer-interrupt context and must never spin on a lock
    /// that ordinary (non-interrupt) code elsewhere might hold for a
    /// non-trivial time (e.g. while routing a pub/sub message through this
    /// same graph) -- returns `None` (treated as "not confirmed yet", the
    /// same as `node_id` simply not existing) rather than risk an
    /// unbounded wait. See `dag_sched::dp_partition::segment_gate_satisfied`'s
    /// own doc.
    pub fn get_node_task_id(&self, node_id: u32) -> Option<u32> {
        let node_idx = to_node_index(node_id);
        let mut node = MCSNode::new();
        let graph = self.graph.try_lock(&mut node)?;
        graph.node_weight(node_idx).map(|info| info.task_id)
    }

    fn add_node_with_topic_edges(
        &self,
        subscribe_topic_names: &[Cow<'static, str>],
        publish_topic_names: &[Cow<'static, str>],
    ) -> NodeIndex {
        let add_node_info = NodeInfo {
            task_id: 0, // Temporary task_id
            subscribe_topic_names: subscribe_topic_names.to_vec(),
            publish_topic_names: publish_topic_names.to_vec(),
            relative_deadline: None,
            priority: None,
            num_finished: 0,
            deadline_job: None,
        };

        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        let add_node_idx = graph.add_node(add_node_info);

        let subscribe_topic_set: BTreeSet<_> = subscribe_topic_names.iter().collect();
        let publish_topic_set: BTreeSet<_> = publish_topic_names.iter().collect();

        if subscribe_topic_names.len() != subscribe_topic_set.len() {
            let mut node = MCSNode::new();
            let mut duplicate_subscribe_nodes = DUPLICATE_SUBSCRIBE_NODES.lock(&mut node);
            duplicate_subscribe_nodes
                .entry(self.id)
                .or_default()
                .push(add_node_idx.index());
        }
        if publish_topic_names.len() != publish_topic_set.len() {
            let mut node = MCSNode::new();
            let mut duplicate_publish_nodes = DUPLICATE_PUBLISH_NODES.lock(&mut node);
            duplicate_publish_nodes
                .entry(self.id)
                .or_default()
                .push(add_node_idx.index());
        }

        let edges_to_add: Vec<_> = graph
            .node_references()
            .flat_map(|node_ref| {
                let node_info = node_ref.weight();

                let edges_from = node_info
                    .subscribe_topic_names
                    .iter()
                    .filter(|topic| publish_topic_set.contains(*topic))
                    .map(move |topic| (add_node_idx, node_ref.id(), topic.clone()));

                let edges_to = node_info
                    .publish_topic_names
                    .iter()
                    .filter(|topic| subscribe_topic_set.contains(*topic))
                    .map(move |topic| (node_ref.id(), add_node_idx, topic.clone()));

                edges_to.chain(edges_from).collect::<Vec<_>>()
            })
            .collect();

        for (from, to, topic_name) in edges_to_add {
            graph.add_edge(from, to, EdgeInfo { topic_name });
        }

        add_node_idx
    }

    pub async fn register_reactor<F, Args, Ret>(
        &self,
        reactor_name: Cow<'static, str>,
        f: F,
        subscribe_topic_names: Vec<Cow<'static, str>>,
        publish_topic_names: Vec<Cow<'static, str>>,
        sched_type: SchedulerType,
    ) where
        F: Fn(
                <Args::Subscribers as MultipleReceiver>::Item,
            ) -> <Ret::Publishers as MultipleSender>::Item
            + Send
            + 'static,
        Args: VectorToSubscribers,
        Ret: VectorToPublishers,
        Ret::Publishers: Send,
        Args::Subscribers: Send,
        <Args::Subscribers as MultipleReceiver>::Item: TupleSize,
        <Ret::Publishers as MultipleSender>::Item: TupleSize,
    {
        let node_idx = self.add_node_with_topic_edges(&subscribe_topic_names, &publish_topic_names);
        self.check_subscribe_mismatch::<Args>(&subscribe_topic_names, node_idx);
        self.check_publish_mismatch::<Ret>(&publish_topic_names, node_idx);

        // To prevent errors caused by ownership moves
        let dag_id = self.id;
        let node_id = node_idx.index() as u32;

        let mut node = MCSNode::new();
        let mut pending_tasks = PENDING_TASKS.lock(&mut node);
        pending_tasks
            .entry(self.id)
            .or_default()
            .push(PendingTask::new(node_idx, move || {
                Box::pin(async move {
                    spawn_reactor::<F, Args, Ret>(
                        reactor_name,
                        f,
                        subscribe_topic_names,
                        publish_topic_names,
                        sched_type,
                        DagInfo::new(dag_id, node_id),
                    )
                    .await
                })
            }));
    }

    pub async fn register_periodic_reactor<F, Ret>(
        &self,
        reactor_name: Cow<'static, str>,
        f: F,
        publish_topic_names: Vec<Cow<'static, str>>,
        sched_type: SchedulerType,
        period: Duration,
    ) where
        F: Fn() -> <Ret::Publishers as MultipleSender>::Item + Send + 'static,
        Ret: VectorToPublishers,
        Ret::Publishers: Send,
        <Ret::Publishers as MultipleSender>::Item: TupleSize,
    {
        let node_idx = self.add_node_with_topic_edges(&Vec::new(), &publish_topic_names);
        self.check_publish_mismatch::<Ret>(&publish_topic_names, node_idx);

        let measure_f: Option<MeasureF> = {
            #[cfg(feature = "perf")]
            {
                Some(performance::create_release_recorder(self.id))
            }
            #[cfg(not(feature = "perf"))]
            {
                None
            }
        };

        // To prevent errors caused by ownership moves
        let dag_id = self.id;
        let node_id = node_idx.index() as u32;

        let mut node = MCSNode::new();
        let mut source_pending_tasks = SOURCE_PENDING_TASKS.lock(&mut node);
        source_pending_tasks.insert(
            self.id,
            PendingTask::new(node_idx, move || {
                Box::pin(async move {
                    spawn_periodic_reactor::<F, Ret>(
                        reactor_name,
                        f,
                        publish_topic_names,
                        sched_type,
                        period,
                        measure_f,
                        DagInfo::new(dag_id, node_id),
                    )
                    .await
                })
            }),
        );
    }

    pub async fn register_sink_reactor<F, Args>(
        &self,
        reactor_name: Cow<'static, str>,
        f: F,
        subscribe_topic_names: Vec<Cow<'static, str>>,
        sched_type: SchedulerType,
        relative_deadline: Duration,
    ) where
        F: Fn(<Args::Subscribers as MultipleReceiver>::Item) + Send + 'static,
        Args: VectorToSubscribers,
        Args::Subscribers: Send,
        <Args::Subscribers as MultipleReceiver>::Item: TupleSize,
    {
        let node_idx = self.add_node_with_topic_edges(&subscribe_topic_names, &Vec::new());
        self.set_relative_deadline(node_idx, relative_deadline);
        self.check_subscribe_mismatch::<Args>(&subscribe_topic_names, node_idx);

        let measure_f = {
            #[cfg(feature = "perf")]
            {
                let dag_id = self.id;
                move |arg: <Args::Subscribers as MultipleReceiver>::Item| {
                    f(arg);
                    performance::record_response_time(dag_id);
                }
            }
            #[cfg(not(feature = "perf"))]
            {
                move |arg: <Args::Subscribers as MultipleReceiver>::Item| {
                    f(arg);
                }
            }
        };

        // To prevent errors caused by ownership moves
        let dag_id = self.id;
        let node_id = node_idx.index() as u32;

        let mut node = MCSNode::new();
        let mut pending_tasks = PENDING_TASKS.lock(&mut node);
        pending_tasks
            .entry(self.id)
            .or_default()
            .push(PendingTask::new(node_idx, move || {
                Box::pin(async move {
                    spawn_sink_reactor::<_, Args>(
                        reactor_name,
                        measure_f,
                        subscribe_topic_names,
                        sched_type,
                        DagInfo::new(dag_id, node_id),
                    )
                    .await
                })
            }));
    }

    fn check_subscribe_mismatch<Args>(
        &self,
        subscribe_topic_names: &[Cow<'static, str>],
        node_idx: NodeIndex,
    ) where
        Args: VectorToSubscribers,
        <Args::Subscribers as MultipleReceiver>::Item: TupleSize,
    {
        if <Args::Subscribers as MultipleReceiver>::Item::SIZE != subscribe_topic_names.len() {
            let mut node = MCSNode::new();
            let mut mismatch_subscribe_nodes = MISMATCH_SUBSCRIBE_NODES.lock(&mut node);
            mismatch_subscribe_nodes
                .entry(self.id)
                .or_default()
                .push(node_idx.index());
        }
    }

    fn check_publish_mismatch<Ret>(
        &self,
        publish_topic_names: &[Cow<'static, str>],
        node_idx: NodeIndex,
    ) where
        Ret: VectorToPublishers,
        <Ret::Publishers as MultipleSender>::Item: TupleSize,
    {
        if <Ret::Publishers as MultipleSender>::Item::SIZE != publish_topic_names.len() {
            let mut node = MCSNode::new();
            let mut mismatch_publish_nodes = MISMATCH_PUBLISH_NODES.lock(&mut node);
            mismatch_publish_nodes
                .entry(self.id)
                .or_default()
                .push(node_idx.index());
        }
    }

    /// Returns the absolute deadline of the job that the node at `node_idx` processes next.
    /// If that job is not released and `release` is true, the source node releases it with
    /// the value of `release_deadline`. Any other wake gets that value without a release.
    pub(crate) fn get_or_release_absolute_deadline(
        &self,
        node_idx: NodeIndex,
        release: bool,
        release_deadline: impl FnOnce() -> u64,
    ) -> u64 {
        let mut node = MCSNode::new();
        let mut absolute_deadlines = self.absolute_deadlines.lock(&mut node);

        let (job, release) = {
            let mut graph_node = MCSNode::new();
            let mut graph = self.graph.lock(&mut graph_node);
            let is_source = graph
                .neighbors_directed(node_idx, Direction::Incoming)
                .next()
                .is_none();
            let node_info = graph.node_weight_mut(node_idx).unwrap();
            let job = node_info.num_finished;
            let release = release && is_source;
            node_info.deadline_job =
                (release || absolute_deadlines.contains_key(&job)).then_some(job);
            (job, release)
        };

        if let Some(&deadline) = absolute_deadlines.get(&job) {
            return deadline;
        }

        let release_deadline = release_deadline();
        if release {
            absolute_deadlines.insert(job, release_deadline);
        }
        release_deadline
    }

    /// Returns true if a wake of the node at `node_idx` in `state` releases a new job, i.e. the
    /// same condition under which [`Dag::get_or_release_absolute_deadline`] releases one.
    /// Call it before that function, which records the release.
    fn is_job_release(&self, node_idx: NodeIndex, state: State) -> bool {
        if state == State::Preempted {
            return false;
        }

        let mut node = MCSNode::new();
        let absolute_deadlines = self.absolute_deadlines.lock(&mut node);

        let mut graph_node = MCSNode::new();
        let graph = self.graph.lock(&mut graph_node);
        let is_source = graph
            .neighbors_directed(node_idx, Direction::Incoming)
            .next()
            .is_none();
        is_source
            && graph
                .node_weight(node_idx)
                .is_some_and(|node_info| !absolute_deadlines.contains_key(&node_info.num_finished))
    }

    /// Returns true if the job that the node at `node_idx` processes is released, but the
    /// last wake of the node did not get its deadline. This occurs if `recv_all` finds the input
    /// in the queue and returns without `wake_task`. A yield then gives the node the deadline.
    fn has_stale_deadline(&self, node_idx: NodeIndex) -> bool {
        let mut node = MCSNode::new();
        let absolute_deadlines = self.absolute_deadlines.lock(&mut node);

        let mut graph_node = MCSNode::new();
        let graph = self.graph.lock(&mut graph_node);
        let node_info = graph.node_weight(node_idx).unwrap();
        node_info.deadline_job != Some(node_info.num_finished)
            && absolute_deadlines.contains_key(&node_info.num_finished)
    }

    /// Records that the node at `node_idx` finished its current job.
    fn finish_job(&self, node_idx: NodeIndex) {
        let mut node = MCSNode::new();
        let mut absolute_deadlines = self.absolute_deadlines.lock(&mut node);

        let mut graph_node = MCSNode::new();
        let mut graph = self.graph.lock(&mut graph_node);
        let node_info = graph.node_weight_mut(node_idx).unwrap();
        node_info.num_finished += 1;

        let oldest_unfinished = graph
            .node_indices()
            .filter_map(|idx| graph.node_weight(idx))
            .map(|node_info| node_info.num_finished)
            .min()
            .unwrap();
        absolute_deadlines.retain(|&job, _| job >= oldest_unfinished);

        // A node whose task ended, for example by a panic, stops counting. Flow control keeps
        // every running node at most `queue_size + 1` jobs behind its upstream node, so an
        // entry beyond this cap belongs only to such a node.
        let max_unfinished = graph.node_count() * (Attribute::default().queue_size + 1) + 1;
        while absolute_deadlines.len() > max_unfinished {
            absolute_deadlines.pop_first();
        }
    }
}

struct PendingTask {
    node_idx: NodeIndex,
    spawn: Box<dyn FnOnce() -> Pin<Box<dyn Future<Output = u32> + Send>> + Send>,
}

impl PendingTask {
    fn new<F>(node_idx: NodeIndex, spawn_fn: F) -> Self
    where
        F: FnOnce() -> Pin<Box<dyn Future<Output = u32> + Send>> + Send + 'static,
    {
        Self {
            node_idx,
            spawn: Box::new(spawn_fn),
        }
    }
}

struct NodeInfo {
    task_id: u32,
    subscribe_topic_names: Vec<Cow<'static, str>>,
    publish_topic_names: Vec<Cow<'static, str>>,
    relative_deadline: Option<Duration>,
    /// Scheduling-policy priority for this node (e.g. a laxity value, or any
    /// other node-importance metric a `dag_sched` policy computes), opaque
    /// to `dag.rs` itself: higher sorts first, mirroring
    /// [`crate::scheduler::SchedulerType::PrioritizedFIFO`]'s convention.
    /// `None` (the default) is treated as `0` (lowest) by
    /// [`get_node_priority`]. Set via [`Dag::set_node_priority`].
    priority: Option<u64>,
    num_finished: u64,         // Number of DAG jobs that this node finished.
    deadline_job: Option<u64>, // Job whose deadline the last wake of this node got.
}

pub fn to_node_index(index: u32) -> NodeIndex {
    NodeIndex::new(index as usize)
}

struct EdgeInfo {
    topic_name: Cow<'static, str>,
}

/// DAGs.
struct Dags {
    candidate_id: u32, // Next candidate of Dag ID.
    id_to_dag: BTreeMap<u32, Arc<Dag>>,
}

impl Dags {
    const fn new() -> Self {
        Self {
            candidate_id: 1,
            id_to_dag: BTreeMap::new(),
        }
    }

    fn create(&mut self) -> Arc<Dag> {
        let mut id = self.candidate_id;
        loop {
            // Find an unused DAG ID.
            if let btree_map::Entry::Vacant(e) = self.id_to_dag.entry(id) {
                let dag = Arc::new(Dag {
                    id,
                    graph: Mutex::new(graph::Graph::new()),
                    absolute_deadlines: Mutex::new(BTreeMap::new()),

                    #[cfg(feature = "perf")]
                    response_info: Mutex::new(ResponseInfo::new()),
                });

                e.insert(dag.clone());
                self.candidate_id = id;

                return dag;
            } else {
                // The candidate DAG ID is already used.
                // Check next candidate.
                // If it overflows, start from 1.
                id = id.wrapping_add(1).max(1);
            }
        }
    }

    #[inline(always)]
    fn remove(&mut self, id: u32) {
        self.id_to_dag.remove(&id);
    }
}

pub fn create_dag() -> Arc<Dag> {
    let mut node = MCSNode::new();
    let mut dags = DAGS.lock(&mut node);
    dags.create()
}

pub fn get_dag(id: u32) -> Option<Arc<Dag>> {
    let mut node = MCSNode::new();
    let dags = DAGS.lock(&mut node);
    dags.id_to_dag.get(&id).cloned()
}

/// Look up the scheduling-policy priority set via [`Dag::set_node_priority`]
/// for `(dag_id, node_id)`, defaulting to `0` (lowest) if unset, or if the
/// DAG or node cannot be found. Used by the GEDF/ClusteredEDF run queues to
/// order same-deadline nodes; regular (non-DAG) tasks are never looked up
/// here and are treated as priority `0` by their callers instead.
pub fn get_node_priority(dag_id: u32, node_id: u32) -> u64 {
    let Some(dag) = get_dag(dag_id) else {
        return 0;
    };
    let node_idx = to_node_index(node_id);
    let mut node = MCSNode::new();
    let graph = dag.graph.lock(&mut node);
    graph
        .node_weight(node_idx)
        .and_then(|info| info.priority)
        .unwrap_or(0)
}

/// `(dag_id, src_node_id, dst_node_id)` of every edge of every registered DAG.
///
/// Used by the trace dump (`task::trace::dump_to_console`) so the host can
/// reconstruct the DAG topology (e.g. critical-path analysis) from a serial
/// log alone.  Node ids match `DagInfo::node_id`.
pub fn get_all_dag_edges() -> Vec<(u32, u32, u32)> {
    let dags = {
        let mut node = MCSNode::new();
        let dags = DAGS.lock(&mut node);
        dags.id_to_dag
            .iter()
            .map(|(id, dag)| (*id, dag.clone()))
            .collect::<Vec<_>>()
    };

    let mut edges = Vec::new();
    for (id, dag) in dags {
        let mut node = MCSNode::new();
        let graph = dag.graph.lock(&mut node);
        for e in graph.edge_references() {
            edges.push((id, e.source().index() as u32, e.target().index() as u32));
        }
    }
    edges
}

/// Returns the absolute deadline of the DAG job that the node of `dag_info` processes next.
/// A wake of the source node in any `state` except `State::Preempted` releases that job
/// with `wake_time` plus the sink relative deadline, if it is not released yet. Any other wake
/// before the release gets that value without a release.
///
/// Each job keeps its own deadline (see [`Dag::get_or_release_absolute_deadline`]), so two jobs
/// of an arbitrary-deadline DAG (relative deadline `D` > period `T`) in flight at once do not
/// clobber each other's deadline.
///
/// # Panics
///
/// Panics if the DAG does not exist, has no node `dag_info.node_id`, or has no sink relative
/// deadline.
pub fn calculate_and_update_dag_deadline(dag_info: &DagInfo, wake_time: u64, state: State) -> u64 {
    let dag_id = dag_info.dag_id;
    let dag = get_dag(dag_id).unwrap_or_else(|| panic!("DAG {dag_id} not found"));

    // The wake of a preempted task resumes it and does not release a job. Any other wake
    // of the source node at an unreleased job must come from its `Interval` tick. After the
    // source node finishes a job, it waits only for that tick, because it has no subscriber.
    let release = state != State::Preempted;

    dag.get_or_release_absolute_deadline(to_node_index(dag_info.node_id), release, || {
        // Microseconds, the unit of `awkernel_lib::delay::uptime()`.
        let relative_deadline_us = dag
            .get_sink_relative_deadline()
            .map(|deadline| deadline.as_micros() as u64)
            .unwrap_or_else(|| panic!("DAG {dag_id} has no sink relative deadline set"));
        wake_time + relative_deadline_us
    })
}

/// True if this wake is the moment `dag_info`'s DAG releases a new job, i.e. the same
/// condition under which [`calculate_and_update_dag_deadline`] releases one: the source
/// node wakes in any `state` except `State::Preempted` at a job that is not released yet.
/// Exposed so scheduler mechanisms that must react to "a new job just started" (e.g.
/// `scheduler::active_vp`'s per-job budget replenishment) do not have to duplicate this
/// DAG-structure lookup. Call it before [`calculate_and_update_dag_deadline`], which
/// records the release. Returns `false` if the DAG is unknown rather than panicking, since
/// a scheduler's wake path must not panic on this check.
pub(crate) fn is_job_release_wake(dag_info: &DagInfo, state: State) -> bool {
    let Some(dag) = get_dag(dag_info.dag_id) else {
        return false;
    };
    dag.is_job_release(to_node_index(dag_info.node_id), state)
}

pub async fn finish_create_dags(dags: &[Arc<Dag>]) -> Result<(), Vec<DagError>> {
    match validate_all_rules(dags) {
        Ok(()) => {
            for dag in dags {
                spawn_dag(dag).await;
            }
            Ok(())
        }
        Err(errors) => {
            for dag in dags {
                remove_dag(dag.id);
            }
            Err(errors)
        }
    }
}

fn remove_dag(id: u32) {
    let mut dags_node = MCSNode::new();
    let mut dags = DAGS.lock(&mut dags_node);
    dags.remove(id);

    let mut pending_node = MCSNode::new();
    let mut pending_tasks = PENDING_TASKS.lock(&mut pending_node);
    pending_tasks.remove(&id);

    let mut source_pending_node = MCSNode::new();
    let mut source_pending_tasks = SOURCE_PENDING_TASKS.lock(&mut source_pending_node);
    source_pending_tasks.remove(&id);
}

fn validate_all_rules(dags: &[Arc<Dag>]) -> Result<(), Vec<DagError>> {
    let mut errors: Vec<DagError> = Vec::new();

    for dag in dags {
        // Skip DAG validation if an arity mismatch is found, as it's the root cause of potential subsequent errors.
        if let Err(arg_errors) = check_for_arity_mismatches(dag.id) {
            errors.extend(arg_errors);
        } else if let Err(dag_validation_error) = validate_dag(dag) {
            errors.push(dag_validation_error);
        } else if let Err(pubsub_duplicate_errors) = check_for_pubsub_duplicates(dag.id) {
            errors.extend(pubsub_duplicate_errors);
        } else if let Err(duplicate_error) = validate_single_publisher_per_topic(dag) {
            errors.extend(duplicate_error);
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }

    validate_dag_topic_conflicts()?;

    Ok(())
}

fn validate_dag_topic_conflicts() -> Result<(), Vec<DagError>> {
    let mut topic_to_dags: BTreeMap<Cow<'static, str>, Vec<u32>> = BTreeMap::new();

    {
        let mut node = MCSNode::new();
        let dags = DAGS.lock(&mut node);

        for dag in dags.id_to_dag.values() {
            let mut node = MCSNode::new();
            let graph = dag.graph.lock(&mut node);
            for edge_ref in graph.edge_references() {
                topic_to_dags
                    .entry(edge_ref.weight().topic_name.clone())
                    .or_default()
                    .push(dag.id);
            }
        }
    }

    let errors: Vec<_> = topic_to_dags
        .into_iter()
        .filter_map(|(topic, mut dag_ids)| {
            dag_ids.sort_unstable();
            dag_ids.dedup();

            if dag_ids.len() > 1 {
                Some(DagError::InterDagTopicConflict(topic, dag_ids))
            } else {
                None
            }
        })
        .collect();

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn validate_dag(dag: &Dag) -> Result<(), DagError> {
    let dag_id = dag.id;
    assert!(
        get_dag(dag_id).is_some(),
        "Invariant Violation: DAG with id {dag_id} must exist, but was not found.",
    );

    let mut pending_node = MCSNode::new();
    if PENDING_TASKS.lock(&mut pending_node).get(&dag_id).is_none() {
        return Err(DagError::MissingPendingTasks(dag_id));
    }

    {
        let mut graph_node = MCSNode::new();
        let graph = dag.graph.lock(&mut graph_node);
        if connected_components(&*graph) != 1 {
            return Err(DagError::NotWeaklyConnected(dag_id));
        }
        if is_cyclic_directed(&*graph) {
            return Err(DagError::ContainsCycle(dag_id));
        }
    }

    if dag.get_source_nodes().len() > 1 {
        return Err(DagError::MultipleSourceNodes(dag_id));
    }
    if dag.get_sink_nodes().len() > 1 {
        return Err(DagError::MultipleSinkNodes(dag_id));
    }

    validate_edge_connect(dag)?;
    Ok(())
}

/// NOTE: On the architecture for this arity validation.
///
/// Ideally, this validation would be performed at an earlier stage, such as inside
/// the `impl_tuple_to_pub_sub` macro in `pubsub.rs`.
///
/// However, that approach would perform the check after the reactor is already spawned.
/// This would limit error handling to just stopping the affected reactor, and implementing
/// a full cleanup of all related DAG data and other reactors would be overly complex.
///
/// Therefore, we adopted the current architecture: errors are first recorded
/// to a `static` variable, and then collected and reported in a batch by this function.
fn check_for_arity_mismatches(dag_id: u32) -> Result<(), Vec<DagError>> {
    let mut node = MCSNode::new();

    let errors: Vec<_> = {
        let subscribe_errors = MISMATCH_SUBSCRIBE_NODES
            .lock(&mut node)
            .remove(&dag_id)
            .unwrap_or_default()
            .into_iter()
            .map(|node_id| DagError::SubscribeArityMismatch(dag_id, node_id));

        let publish_errors = MISMATCH_PUBLISH_NODES
            .lock(&mut node)
            .remove(&dag_id)
            .unwrap_or_default()
            .into_iter()
            .map(|node_id| DagError::PublishArityMismatch(dag_id, node_id));

        subscribe_errors.chain(publish_errors).collect()
    };

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// Ideally, this validation would be performed at an earlier stage, such as inside
/// the `add_node_with_topic_edges()`.
///
/// However, that approach would force the caller to handle a Result on every
/// single node addition, making the API cumbersome, and implementing
/// a full cleanup of all related DAG data and other reactors would be overly complex.
///
/// Therefore, we adopted the current architecture: errors are first recorded
/// to a `static` variable, and then collected and reported in a batch by this function.
fn check_for_pubsub_duplicates(dag_id: u32) -> Result<(), Vec<DagError>> {
    let mut node = MCSNode::new();

    let errors: Vec<_> = {
        let subscribe_errors = DUPLICATE_SUBSCRIBE_NODES
            .lock(&mut node)
            .remove(&dag_id)
            .unwrap_or_default()
            .into_iter()
            .map(|node_id| DagError::DuplicateSubscribe(dag_id, node_id));

        let publish_errors = DUPLICATE_PUBLISH_NODES
            .lock(&mut node)
            .remove(&dag_id)
            .unwrap_or_default()
            .into_iter()
            .map(|node_id| DagError::DuplicatePublish(dag_id, node_id));

        subscribe_errors.chain(publish_errors).collect()
    };

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// This validation prevents issues caused by the following misconfigurations:
/// - Message Loss: A published topic is not subscribed to by any reactor.
/// - Indefinite Wait: A subscribed topic has no corresponding publisher.
fn validate_edge_connect(dag: &Dag) -> Result<(), DagError> {
    type DagErrorFn = fn(u32, usize) -> DagError;

    let mut node = MCSNode::new();
    let graph = dag.graph.lock(&mut node);
    for node_idx in graph.node_indices() {
        let node_info = graph.node_weight(node_idx).unwrap();
        for direction in [Direction::Incoming, Direction::Outgoing] {
            let (expect_count, error) = match direction {
                Direction::Incoming => (
                    node_info.subscribe_topic_names.len(),
                    DagError::NoPublisherFound as DagErrorFn,
                ),
                Direction::Outgoing => (
                    node_info.publish_topic_names.len(),
                    DagError::NoSubscriberFound as DagErrorFn,
                ),
            };

            let actual_count = graph.neighbors_directed(node_idx, direction).count();
            if actual_count < expect_count {
                return Err(error(dag.id, node_idx.index()));
            }
        }
    }

    Ok(())
}

/// To simplify the current system design and management,
/// we have adopted a rule that only one publisher is allowed per topic.
///
/// Note:
/// This restriction may need to be relaxed in the future to support use cases
/// where multiple publishers need to publish to a single, common topic.
fn validate_single_publisher_per_topic(dag: &Dag) -> Result<(), Vec<DagError>> {
    let mut node = MCSNode::new();
    let graph = dag.graph.lock(&mut node);

    let publisher_counts_by_topic = graph.edge_references().fold(
        BTreeMap::<Cow<'static, str>, usize>::new(),
        |mut acc, edge| {
            *acc.entry(edge.weight().topic_name.clone()).or_insert(0) += 1;
            acc
        },
    );

    let errors: Vec<_> = publisher_counts_by_topic
        .into_iter()
        .filter(|(_, count)| *count > 1)
        .map(|(topic, _)| DagError::TopicHasMultiplePublishers(dag.id, topic))
        .collect();

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

async fn spawn_dag(dag: &Arc<Dag>) {
    let dag_id = dag.id;
    let pending_tasks = {
        let mut node = MCSNode::new();
        let mut pending_tasks = PENDING_TASKS.lock(&mut node);
        pending_tasks.remove(&dag_id).unwrap()
    };

    for task in pending_tasks {
        let task_id = (task.spawn)().await;
        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);
        if let Some(node_info) = graph.node_weight_mut(task.node_idx) {
            node_info.task_id = task_id;
        }
    }

    // To prevent message drops, source reactor is spawned after all subsequent reactors have been spawned.
    // If the source reactor is not spawned last, it may publish a message before subsequent reactors are ready to receive it.
    let source_pending_task = {
        let mut node = MCSNode::new();
        let mut source_pending_tasks = SOURCE_PENDING_TASKS.lock(&mut node);
        source_pending_tasks.remove(&dag_id).unwrap()
    };

    let task_id = (source_pending_task.spawn)().await;
    let mut node = MCSNode::new();
    let mut graph = dag.graph.lock(&mut node);
    if let Some(node_info) = graph.node_weight_mut(source_pending_task.node_idx) {
        node_info.task_id = task_id;
    }
}

async fn spawn_reactor<F, Args, Ret>(
    reactor_name: Cow<'static, str>,
    f: F,
    subscribe_topic_names: Vec<Cow<'static, str>>,
    publish_topic_names: Vec<Cow<'static, str>>,
    sched_type: SchedulerType,
    dag_info: DagInfo,
) -> u32
where
    F: Fn(
            <Args::Subscribers as MultipleReceiver>::Item,
        ) -> <Ret::Publishers as MultipleSender>::Item
        + Send
        + 'static,
    Args: VectorToSubscribers,
    Ret: VectorToPublishers,
    Ret::Publishers: Send,
    Args::Subscribers: Send,
{
    // A separate handle to the same counter as `dag_info.period_index`: the
    // closure below only touches this field, so capturing the Arc directly
    // (rather than the whole `dag_info`) leaves `dag_info` itself intact for
    // the `spawn_with_dag_info` call after the closure is built.
    #[cfg(feature = "period-index-propagation")]
    let period_index_cell = dag_info.period_index.clone();
    let dag = get_dag(dag_info.dag_id).unwrap();
    let node_idx = to_node_index(dag_info.node_id);

    // Subscribe before `spawn_dag` spawns the source node. A message published before the
    // subscription is lost.
    let subscribers: <Args as VectorToSubscribers>::Subscribers =
        Args::create_subscribers(subscribe_topic_names, Attribute::default());

    let future = async move {
        let publishers = <Ret as VectorToPublishers>::create_publishers(
            publish_topic_names,
            Attribute::default(),
        );

        loop {
            #[cfg(feature = "period-index-propagation")]
            {
                let (args, period_index): (
                    <<Args as VectorToSubscribers>::Subscribers as MultipleReceiver>::Item,
                    u32,
                ) = subscribers.recv_all_with_period_index().await;
                period_index_cell.store(period_index, core::sync::atomic::Ordering::Release);

                // [end] pubsub communication latency
                let end = awkernel_lib::time::Time::now().uptime().as_nanos() as u64;
                record_subscribe_timestamp(
                    period_index as usize,
                    end,
                    1,
                    dag_info.dag_id,
                    dag_info.node_id,
                );

                if dag.has_stale_deadline(node_idx) {
                    crate::r#yield().await;
                }

                let results = f(args);
                publishers
                    .send_all_with_period_index(
                        results,
                        1,
                        period_index as usize,
                        dag_info.dag_id,
                        dag_info.node_id,
                    )
                    .await;
            }

            #[cfg(not(feature = "period-index-propagation"))]
            {
                let args: <<Args as VectorToSubscribers>::Subscribers as MultipleReceiver>::Item =
                    subscribers.recv_all().await;

                if dag.has_stale_deadline(node_idx) {
                    crate::r#yield().await;
                }

                let results = f(args);
                publishers.send_all(results).await;
            }

            dag.finish_job(node_idx);
        }
    };

    crate::task::spawn_with_dag_info(reactor_name, future, sched_type, dag_info)
}

async fn spawn_periodic_reactor<F, Ret>(
    reactor_name: Cow<'static, str>,
    f: F,
    publish_topic_names: Vec<Cow<'static, str>>,
    sched_type: SchedulerType,
    period: Duration,
    _release_measure: Option<MeasureF>,
    dag_info: DagInfo,
) -> u32
where
    F: Fn() -> <Ret::Publishers as MultipleSender>::Item + Send + 'static,
    Ret: VectorToPublishers,
    Ret::Publishers: Send,
{
    #[cfg(feature = "perf")]
    let (release_measure, periodic_measure) = {
        if let Some(measure) = _release_measure {
            (measure.clone(), measure)
        } else {
            unreachable!("Measure function must be provided for performance tracking.");
        }
    };

    // See `spawn_reactor` for why this is cloned out separately instead of
    // referenced via `dag_info` from inside the closure.
    #[cfg(feature = "period-index-propagation")]
    let period_index_cell = dag_info.period_index.clone();
    let dag = get_dag(dag_info.dag_id).unwrap();
    let node_idx = to_node_index(dag_info.node_id);

    // TODO(sykwer): Improve mechanisms to more closely align performance behavior with the DAG scheduling model.
    let future = async move {
        let publishers = <Ret as VectorToPublishers>::create_publishers(
            publish_topic_names,
            Attribute::default(),
        );

        let mut interval = interval(period, dag_info.dag_id);
        // Consume the first tick here to start the loop's main body without an initial delay.
        interval.tick().await;

        loop {
            #[cfg(feature = "period-index-propagation")]
            {
                let index = get_period_index(dag_info.dag_id) as usize;
                period_index_cell.store(index as u32, core::sync::atomic::Ordering::Release);
                if index != 0 {
                    // [start] cycle deviation index >= 1
                    let release_time = awkernel_lib::time::Time::now().uptime().as_nanos() as u64;
                    update_cycle_start_timestamp(index, release_time, dag_info.dag_id);
                }
                let results = f();
                publishers
                    .send_all_with_period_index(
                        results,
                        0,
                        index,
                        dag_info.dag_id,
                        dag_info.node_id,
                    )
                    .await;
                increment_period_index(dag_info.dag_id);
            }

            #[cfg(not(feature = "period-index-propagation"))]
            {
                let results = f();
                publishers.send_all(results).await;
            }

            dag.finish_job(node_idx);

            #[cfg(feature = "perf")]
            periodic_measure();

            interval.tick().await;
        }
    };

    let task_id = crate::task::spawn_with_dag_info(reactor_name, future, sched_type, dag_info);

    #[cfg(feature = "perf")]
    release_measure();

    task_id
}

async fn spawn_sink_reactor<F, Args>(
    reactor_name: Cow<'static, str>,
    f: F,
    subscribe_topic_names: Vec<Cow<'static, str>>,
    sched_type: SchedulerType,
    dag_info: DagInfo,
) -> u32
where
    F: Fn(<Args::Subscribers as MultipleReceiver>::Item) + Send + 'static,
    Args: VectorToSubscribers,
    Args::Subscribers: Send,
{
    // See `spawn_reactor` for why this is cloned out separately instead of
    // referenced via `dag_info` from inside the closure.
    #[cfg(feature = "period-index-propagation")]
    let period_index_cell = dag_info.period_index.clone();
    let dag = get_dag(dag_info.dag_id).unwrap();
    let node_idx = to_node_index(dag_info.node_id);

    // Subscribe before `spawn_dag` spawns the source node. A message published before the
    // subscription is lost.
    let subscribers: <Args as VectorToSubscribers>::Subscribers =
        Args::create_subscribers(subscribe_topic_names, Attribute::default());

    let future = async move {
        loop {
            #[cfg(feature = "period-index-propagation")]
            {
                let (args, period_index): (<Args::Subscribers as MultipleReceiver>::Item, u32) =
                    subscribers.recv_all_with_period_index().await;
                period_index_cell.store(period_index, core::sync::atomic::Ordering::Release);

                // [end] pubsub communication latency
                let end = awkernel_lib::time::Time::now().uptime().as_nanos() as u64;
                record_subscribe_timestamp(
                    period_index as usize,
                    end,
                    2,
                    dag_info.dag_id,
                    dag_info.node_id,
                );

                let timenow = awkernel_lib::time::Time::now().uptime().as_nanos() as u64;
                if period_index != 0 {
                    update_cycle_end_timestamp(period_index as usize, timenow, dag_info.dag_id);
                }

                if dag.has_stale_deadline(node_idx) {
                    crate::r#yield().await;
                }

                f(args);
            }

            #[cfg(not(feature = "period-index-propagation"))]
            {
                let args: <Args::Subscribers as MultipleReceiver>::Item =
                    subscribers.recv_all().await;

                if dag.has_stale_deadline(node_idx) {
                    crate::r#yield().await;
                }

                f(args);
            }

            dag.finish_job(node_idx);
        }
    };

    crate::task::spawn_with_dag_info(reactor_name, future, sched_type, dag_info)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn late_node_keeps_the_deadline_of_its_job() {
        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &["deadline_test_topic".into()]);
        let sink = dag.add_node_with_topic_edges(&["deadline_test_topic".into()], &[]);

        // A non-source node does not release a job.
        assert_eq!(dag.get_or_release_absolute_deadline(sink, true, || 5), 5);

        // The source node releases job 0. A later wake in job 0 keeps the deadline.
        assert_eq!(
            dag.get_or_release_absolute_deadline(source, true, || 10),
            10
        );
        assert_eq!(
            dag.get_or_release_absolute_deadline(source, true, || 11),
            10
        );

        // The input of job 0 can reach the sink node without a wake.
        assert!(dag.has_stale_deadline(sink));

        dag.finish_job(source);

        // A preempted source node resumes before the next period and does not release job 1.
        assert_eq!(
            dag.get_or_release_absolute_deadline(source, false, || 15),
            15
        );
        assert_eq!(
            dag.get_or_release_absolute_deadline(source, true, || 20),
            20
        );

        // The sink node wakes for job 0 after the release of job 1.
        assert_eq!(dag.get_or_release_absolute_deadline(sink, true, || 21), 10);
        assert!(!dag.has_stale_deadline(sink));

        // The source node released job 1.
        dag.finish_job(sink);
        assert!(dag.has_stale_deadline(sink));
        assert_eq!(dag.get_or_release_absolute_deadline(sink, true, || 22), 20);
        assert!(!dag.has_stale_deadline(sink));
        assert!(!dag
            .absolute_deadlines
            .lock(&mut MCSNode::new())
            .contains_key(&0));
    }

    #[test]
    fn job_release_matches_the_release_of_the_deadline() {
        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &["release_test_topic".into()]);
        let sink = dag.add_node_with_topic_edges(&["release_test_topic".into()], &[]);

        // A non-source node and a preempted source node never release a job.
        assert!(!dag.is_job_release(sink, State::Runnable));
        assert!(!dag.is_job_release(source, State::Preempted));

        // The source node releases job 0. A later wake in job 0 does not release it again.
        assert!(dag.is_job_release(source, State::Runnable));
        dag.get_or_release_absolute_deadline(source, true, || 10);
        assert!(!dag.is_job_release(source, State::Runnable));

        // After the source node finishes job 0, its next wake releases job 1.
        dag.finish_job(source);
        assert!(dag.is_job_release(source, State::Runnable));
    }

    #[test]
    fn deadline_stays_until_every_node_finishes_its_job() {
        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &["retention_test_a".into()]);
        let middle = dag
            .add_node_with_topic_edges(&["retention_test_a".into()], &["retention_test_b".into()]);
        let sink = dag.add_node_with_topic_edges(&["retention_test_b".into()], &[]);

        // The source node releases jobs 0, 1, and 2.
        assert_eq!(
            dag.get_or_release_absolute_deadline(source, true, || 10),
            10
        );
        dag.finish_job(source);
        assert_eq!(
            dag.get_or_release_absolute_deadline(source, true, || 20),
            20
        );
        dag.finish_job(source);
        assert_eq!(
            dag.get_or_release_absolute_deadline(source, true, || 30),
            30
        );

        // The sink node finishes job 0 before the middle node records its finish.
        dag.finish_job(sink);
        assert_eq!(
            dag.get_or_release_absolute_deadline(middle, true, || 31),
            10
        );

        dag.finish_job(middle);
        assert_eq!(
            dag.get_or_release_absolute_deadline(middle, true, || 32),
            20
        );
        assert_eq!(dag.get_or_release_absolute_deadline(sink, true, || 33), 20);

        let mut node = MCSNode::new();
        let jobs: Vec<u64> = dag
            .absolute_deadlines
            .lock(&mut node)
            .keys()
            .copied()
            .collect();
        assert_eq!(jobs, [1, 2]);
    }

    #[test]
    fn deadlines_of_a_stopped_node_are_capped() {
        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &["cap_test_topic".into()]);
        let _sink = dag.add_node_with_topic_edges(&["cap_test_topic".into()], &[]);

        // The sink node stopped, for example by a panic, and the source node keeps releasing.
        for deadline in 0..100 {
            dag.get_or_release_absolute_deadline(source, true, || deadline);
            dag.finish_job(source);
        }

        let mut node = MCSNode::new();
        let absolute_deadlines = dag.absolute_deadlines.lock(&mut node);
        // The cap for two nodes.
        assert_eq!(
            absolute_deadlines.len(),
            2 * (Attribute::default().queue_size + 1) + 1
        );
        assert_eq!(absolute_deadlines.last_key_value(), Some((&99, &99)));
    }
}
