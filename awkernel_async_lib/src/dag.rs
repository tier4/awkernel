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
//! ## 4. Estimated WCET and feasibility
//!
//! Registration methods accept an optional estimated WCET. An absent estimate is treated as zero
//! by DAG validation, which rejects estimates whose longest dependency path exceeds the sink's
//! relative deadline.
//!
//! Validation also records [`TimingInfo`] for each node. These estimates do not change interval-tick
//! job release times or the DAG deadline assignment used by the EDF scheduler.
//!
//! Changing a DAG after timing analysis clears its estimates and emits a warning. Subsequent LLFT
//! wakes order by the real job deadline until the DAG is analyzed again.
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
//! - **Periodic Source**: The source node must be a periodic reactor registered via `register_periodic_reactor`.
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
        visit::{
            dfsvisit::{depth_first_search, DfsEvent},
            EdgeRef, IntoNodeReferences, NodeRef,
        },
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
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::{
    sync::mutex::{MCSNode, Mutex},
    time::Instant,
};
use core::{future::Future, pin::Pin, time::Duration};

#[cfg(target_pointer_width = "64")]
use core::sync::atomic::{AtomicU64, Ordering};

#[cfg(feature = "perf")]
use performance::ResponseInfo;

static DAGS: Mutex<Dags> = Mutex::new(Dags::new()); // Set of DAGs.

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

#[derive(Clone, Debug)]
pub enum DagError {
    NodeNotFound(u32, usize),
    MissingNodeTiming(u32, usize),
    MissingSinkDeadline(u32),
    InfeasibleWcet {
        dag_id: u32,
        critical_path: Option<Duration>,
        deadline: Duration,
    },
    NotWeaklyConnected(u32),
    ContainsCycle(u32),
    MissingPendingTasks(u32),
    MultipleSourceNodes(u32),
    MultipleSinkNodes(u32),
    NoPeriodicSourceNode(u32),
    NoPublisherFound(u32, usize),
    NoSubscriberFound(u32, usize),
    SubscribeArityMismatch(u32, usize),
    PublishArityMismatch(u32, usize),
    DuplicateSubscribe(u32, usize),
    DuplicatePublish(u32, usize),
    TopicHasMultiplePublishers(u32, Cow<'static, str>),
    InterDagTopicConflict(Cow<'static, str>, Vec<u32>),
}

#[rustfmt::skip]
impl core::fmt::Display for DagError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DagError::NodeNotFound(dag_id, node_id) => write!(f, "DAG#{dag_id} Node#{node_id} not found"),
            DagError::MissingNodeTiming(dag_id, node_id) => write!(f, "DAG#{dag_id} Node#{node_id} timing has not been analyzed"),
            DagError::MissingSinkDeadline(dag_id) => write!(f, "DAG#{dag_id} has no sink relative deadline"),
            DagError::InfeasibleWcet { dag_id, critical_path: Some(critical_path), deadline } => {
                write!(f, "DAG#{dag_id}: estimated critical path {critical_path:?} exceeds sink relative deadline {deadline:?}")
            }
            DagError::InfeasibleWcet { dag_id, critical_path: None, deadline } => {
                write!(f, "DAG#{dag_id}: estimated critical path exceeds Duration::MAX (sink relative deadline {deadline:?})")
            }
            DagError::NotWeaklyConnected(dag_id) => write!(f, "DAG#{dag_id} is not weakly connected"),
            DagError::ContainsCycle(dag_id) => write!(f, "DAG#{dag_id} contains a cycle"),
            DagError::MissingPendingTasks(dag_id) => write!(f, "DAG#{dag_id} has missing pending tasks"),
            DagError::MultipleSourceNodes(dag_id) => write!(f, "DAG#{dag_id} has multiple source nodes"),
            DagError::MultipleSinkNodes(dag_id) => write!(f, "DAG#{dag_id} has multiple sink nodes"),
            DagError::NoPeriodicSourceNode(dag_id) => write!(f, "DAG#{dag_id} has no periodic source node"),
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
        }
    }
}

type DagGraph = graph::Graph<NodeInfo, EdgeInfo>;

/// Timing information fixed when a DAG job is released.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct JobInfo {
    /// Source tick target, in microseconds.
    pub(crate) release_time: u64,
    /// Absolute deadline fixed at source release, in microseconds.
    pub(crate) absolute_deadline: u64,
}

impl DagGraph {
    /// Clear cached timing information, returning whether any was present.
    fn clear_timing(&mut self) -> bool {
        let mut cleared = false;
        for idx in self.node_indices() {
            if let Some(info) = self.node_weight_mut(idx) {
                cleared |= info.timing.take().is_some();
            }
        }
        cleared
    }

    #[inline]
    fn get_sink_relative_deadline(&self) -> Option<Duration> {
        let sink_node_index = self.externals(Direction::Outgoing).next()?;
        self.node_weight(sink_node_index).unwrap().relative_deadline
    }

    /// Sets the relative deadline of a node, returning whether the timing information was cleared.
    #[inline]
    fn set_relative_deadline(&mut self, node_idx: NodeIndex, deadline: Duration) -> Option<bool> {
        match self.node_weight_mut(node_idx) {
            Some(info) => {
                info.relative_deadline = Some(deadline);
                Some(self.clear_timing())
            }
            None => None,
        }
    }
}

pub struct Dag {
    id: u32,
    graph: Mutex<DagGraph>,

    /// Timing information for each released job that a node has not finished, keyed by job
    /// number. A job is one run of the DAG. When the periodic source node wakes for its interval
    /// tick, it releases the job at the tick target time, not at the actual wake time.
    jobs: Mutex<BTreeMap<u64, JobInfo>>,

    /// Target time of the source's next interval tick, in microseconds.
    /// `u64::MAX` means the target is not set yet.
    #[cfg(target_pointer_width = "64")]
    next_release_time: AtomicU64,
    #[cfg(target_pointer_width = "32")]
    next_release_time: Mutex<u64>,

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

    /// Returns the relative deadline of the first sink node, or an error if it is missing.
    pub fn get_sink_relative_deadline(&self) -> Result<Duration, DagError> {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        graph
            .get_sink_relative_deadline()
            .ok_or(DagError::MissingSinkDeadline(self.id))
    }

    fn set_relative_deadline(
        &self,
        node_idx: NodeIndex,
        deadline: Duration,
    ) -> Result<(), DagError> {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        let cleared = graph
            .set_relative_deadline(node_idx, deadline)
            .ok_or(DagError::NodeNotFound(self.id, node_idx.index()))?;
        drop(graph);
        if cleared {
            log::warn!(
                "DAG#{} timing estimates were cleared after a deadline change; subsequent LLFT wakes will use real deadlines until timing is analyzed again",
                self.id
            );
        }
        Ok(())
    }

    fn add_node_with_topic_edges(
        &self,
        subscribe_topic_names: &[Cow<'static, str>],
        publish_topic_names: &[Cow<'static, str>],
        wcet: Option<Duration>,
    ) -> NodeIndex {
        let add_node_info = NodeInfo {
            task_id: 0, // Temporary task_id
            subscribe_topic_names: subscribe_topic_names.to_vec(),
            publish_topic_names: publish_topic_names.to_vec(),
            relative_deadline: None,
            wcet,
            timing: None,
            num_finished: 0,
            deadline_job: None,
        };

        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        let cleared = graph.clear_timing();
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

        drop(graph);
        if cleared {
            log::warn!(
                "DAG#{} timing estimates were cleared after node registration; subsequent LLFT wakes will use real deadlines until timing is analyzed again",
                self.id
            );
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
        wcet: Option<Duration>,
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
        let node_idx =
            self.add_node_with_topic_edges(&subscribe_topic_names, &publish_topic_names, wcet);
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
                        DagInfo { dag_id, node_id },
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
        wcet: Option<Duration>,
    ) where
        F: Fn() -> <Ret::Publishers as MultipleSender>::Item + Send + 'static,
        Ret: VectorToPublishers,
        Ret::Publishers: Send,
        <Ret::Publishers as MultipleSender>::Item: TupleSize,
    {
        let node_idx = self.add_node_with_topic_edges(&[], &publish_topic_names, wcet);
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
                        DagInfo { dag_id, node_id },
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
        wcet: Option<Duration>,
    ) where
        F: Fn(<Args::Subscribers as MultipleReceiver>::Item) + Send + 'static,
        Args: VectorToSubscribers,
        Args::Subscribers: Send,
        <Args::Subscribers as MultipleReceiver>::Item: TupleSize,
    {
        let node_idx = self.add_node_with_topic_edges(&subscribe_topic_names, &[], wcet);
        self.set_relative_deadline(node_idx, relative_deadline)
            .unwrap();
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
                        DagInfo { dag_id, node_id },
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

    fn set_next_release_time(&self, target: Instant) {
        let release_time = target.uptime().as_micros() as u64;

        #[cfg(target_pointer_width = "64")]
        self.next_release_time
            .store(release_time, Ordering::Release);

        #[cfg(target_pointer_width = "32")]
        {
            let mut node = MCSNode::new();
            *self.next_release_time.lock(&mut node) = release_time;
        }
    }

    fn load_next_release_time(&self) -> u64 {
        #[cfg(target_pointer_width = "64")]
        {
            self.next_release_time.load(Ordering::Acquire)
        }

        #[cfg(target_pointer_width = "32")]
        {
            let mut node = MCSNode::new();
            let release_time = *self.next_release_time.lock(&mut node);
            release_time
        }
    }

    /// Returns a consistent snapshot of the next job and the node's timing estimates.
    /// If that job is not released and `release` is true, the source node releases it with
    /// its next tick target and the sink's current relative deadline. Other wakes before
    /// release have no job in the snapshot.
    ///
    /// # Panics
    ///
    /// Panics if the source releases a job before its next release time is set.
    fn get_or_release_job(&self, node_idx: NodeIndex, release: bool) -> JobTimingSnapshot {
        let mut node = MCSNode::new();
        let mut jobs = self.jobs.lock(&mut node);

        let (job, release, existing, timing, sink_relative_deadline) = {
            let mut graph_node = MCSNode::new();
            let mut graph = self.graph.lock(&mut graph_node);
            let is_source = graph
                .neighbors_directed(node_idx, Direction::Incoming)
                .next()
                .is_none();
            let node_info = graph.node_weight_mut(node_idx).unwrap();
            let job = node_info.num_finished;
            let release = release && is_source;
            let existing = jobs.get(&job).copied();
            let timing = node_info.timing;
            node_info.deadline_job = (release || existing.is_some()).then_some(job);
            let sink_relative_deadline = if existing.is_none() {
                graph.get_sink_relative_deadline()
            } else {
                None
            };
            (job, release, existing, timing, sink_relative_deadline)
        };

        if let Some(job_info) = existing {
            return JobTimingSnapshot {
                job: Some(job_info),
                timing,
                sink_relative_deadline,
            };
        }

        if release {
            let release_time = self.load_next_release_time();
            assert_ne!(
                release_time,
                u64::MAX,
                "The DAG source released a job before its next release time was set"
            );
            if let Some(relative_deadline) = sink_relative_deadline {
                let relative_deadline_us = relative_deadline.as_micros() as u64;
                let job_info = JobInfo {
                    release_time,
                    absolute_deadline: release_time + relative_deadline_us,
                };
                jobs.insert(job, job_info);
                return JobTimingSnapshot {
                    job: Some(job_info),
                    timing,
                    sink_relative_deadline,
                };
            }
        }

        JobTimingSnapshot {
            job: None,
            timing,
            sink_relative_deadline,
        }
    }

    /// Returns true if the job that the node at `node_idx` processes is released, but the
    /// last wake of the node did not get its deadline. This occurs if `recv_all` finds the input
    /// in the queue and returns without `wake_task`. A yield then gives the node the deadline.
    fn has_stale_deadline(&self, node_idx: NodeIndex) -> bool {
        let mut node = MCSNode::new();
        let jobs = self.jobs.lock(&mut node);

        let mut graph_node = MCSNode::new();
        let graph = self.graph.lock(&mut graph_node);
        let node_info = graph.node_weight(node_idx).unwrap();
        node_info.deadline_job != Some(node_info.num_finished)
            && jobs.contains_key(&node_info.num_finished)
    }

    /// Records that the node at `node_idx` finished its current job.
    fn finish_job(&self, node_idx: NodeIndex) {
        let mut node = MCSNode::new();
        let mut jobs = self.jobs.lock(&mut node);

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
        jobs.retain(|&job, _| job >= oldest_unfinished);

        // A node whose task ended, for example by a panic, stops counting. Flow control keeps
        // every running node at most `queue_size + 1` jobs behind its upstream node, so an
        // entry beyond this cap belongs only to such a node.
        let max_unfinished = graph.node_count() * (Attribute::default().queue_size + 1) + 1;
        while jobs.len() > max_unfinished {
            jobs.pop_first();
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

/// WCET-based estimates relative to the DAG job release, not timing requirements.
/// A missing WCET is retained as zero for the estimates.
///
/// This struct is useful for analyzing the timing characteristics of nodes within a DAG,
/// as well as for defining alternative scheduling strategies based on timing estimates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TimingInfo {
    estimated_wcet: Duration,
    earliest_start: Duration,
    latest_finish: Duration,
    is_in_critical_path: bool,
}

impl TimingInfo {
    /// WCET used in the analysis.
    #[inline]
    pub const fn estimated_wcet(&self) -> Duration {
        self.estimated_wcet
    }

    /// Longest estimated execution path leading up to the node.
    #[inline]
    pub const fn earliest_start(&self) -> Duration {
        self.earliest_start
    }

    /// Earliest start plus the node's estimated WCET.
    #[inline]
    pub fn earliest_finish(&self) -> Duration {
        self.earliest_start + self.estimated_wcet()
    }

    /// Latest finish minus the node's estimated WCET.
    #[inline]
    pub fn latest_start(&self) -> Duration {
        self.latest_finish - self.estimated_wcet()
    }

    /// Latest finish compatible with the sink deadline and successor WCETs.
    pub const fn latest_finish(&self) -> Duration {
        self.latest_finish
    }

    /// Latest finish minus earliest finish; this is static, not runtime laxity.
    #[inline]
    pub fn slack(&self) -> Duration {
        self.latest_finish - self.earliest_finish()
    }

    /// True for every node on any longest estimated WCET path.
    #[inline]
    pub fn is_in_critical_path(&self) -> bool {
        self.is_in_critical_path
    }
}

#[derive(Clone, Copy)]
struct JobTimingSnapshot {
    job: Option<JobInfo>,
    timing: Option<TimingInfo>,
    sink_relative_deadline: Option<Duration>,
}

impl JobTimingSnapshot {
    fn deadline(&self, dag_id: u32, wake_time: u64) -> u64 {
        match self.job {
            Some(job) => job.absolute_deadline,
            None => {
                // Microseconds, the unit of `awkernel_lib::delay::uptime()`.
                let relative_deadline_us = self
                    .sink_relative_deadline
                    .map(|deadline| deadline.as_micros() as u64)
                    .unwrap_or_else(|| panic!("DAG {dag_id} has no sink relative deadline set"));
                wake_time + relative_deadline_us
            }
        }
    }

    fn latest_finish_priority(&self, dag_id: u32, wake_time: u64) -> (u64, u64) {
        let deadline = self.deadline(dag_id, wake_time);
        let ordering_time = match (self.job, self.timing) {
            (Some(job), Some(timing)) => {
                let offset = timing.latest_finish().as_micros() as u64;
                job.release_time + offset
            }
            _ => deadline,
        };
        (deadline, ordering_time)
    }
}

struct NodeInfo {
    task_id: u32,
    subscribe_topic_names: Vec<Cow<'static, str>>,
    publish_topic_names: Vec<Cow<'static, str>>,
    relative_deadline: Option<Duration>,
    wcet: Option<Duration>,
    timing: Option<TimingInfo>,
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
                    jobs: Mutex::new(BTreeMap::new()),
                    #[cfg(target_pointer_width = "64")]
                    next_release_time: AtomicU64::new(u64::MAX),
                    #[cfg(target_pointer_width = "32")]
                    next_release_time: Mutex::new(u64::MAX),

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

fn dag_job_timing(dag_info: &DagInfo, state: State) -> JobTimingSnapshot {
    let dag_id = dag_info.dag_id;
    let dag = get_dag(dag_id).unwrap_or_else(|| panic!("DAG {dag_id} not found"));
    // The wake of a preempted task resumes it and does not release a job. Any other wake
    // of the source node at an unreleased job must come from its `Interval` tick. After the
    // source node finishes a job, it waits only for that tick, because it has no subscriber.
    dag.get_or_release_job(to_node_index(dag_info.node_id), state != State::Preempted)
}

/// Returns the absolute deadline of the DAG job that the node of `dag_info` processes next.
/// A source wake in any `state` except `State::Preempted` releases an unreleased job. Its
/// absolute deadline is fixed at release to the interval tick target plus the sink relative
/// deadline. A wake before release gets `wake_time` plus the current sink relative deadline.
///
/// # Panics
///
/// Panics if the DAG does not exist, has no node `dag_info.node_id`, or has no sink relative
/// deadline, or the source releases a job without an interval tick target.
pub(crate) fn calculate_and_update_dag_deadline(
    dag_info: &DagInfo,
    wake_time: u64,
    state: State,
) -> u64 {
    dag_job_timing(dag_info, state).deadline(dag_info.dag_id, wake_time)
}

/// Keep the real deadline separate from the latest-finish ordering key.
/// If the job or timing is unavailable, or the key overflows, order by the
/// real deadline until explicit error reporting is supported.
pub(crate) fn calculate_dag_latest_finish_priority(
    dag_info: &DagInfo,
    wake_time: u64,
    state: State,
) -> (u64, u64) {
    dag_job_timing(dag_info, state).latest_finish_priority(dag_info.dag_id, wake_time)
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
        } else if let Err(timing_error) = compute_timing(dag) {
            errors.push(timing_error);
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

    {
        let mut source_pending_node = MCSNode::new();
        if SOURCE_PENDING_TASKS
            .lock(&mut source_pending_node)
            .get(&dag_id)
            .is_none()
        {
            return Err(DagError::NoPeriodicSourceNode(dag_id));
        }
    }

    validate_edge_connect(dag)?;
    Ok(())
}

/// Checks feasibility and calculates node timing estimates.
/// This runs during DAG setup, not in the scheduler or reactor execution paths.
///
/// A forward pass computes `EF(v) = max(EF(p)) + C(v)` over predecessors, including the
/// sink's own WCET.
///
/// A backward pass computes `LS(v) = min(LS(s)) - C(v)` over successors, starting from
/// the sink's deadline.
fn compute_timing(dag: &Dag) -> Result<(), DagError> {
    let dag_id = dag.id;
    let mut node = MCSNode::new();
    let mut graph = dag.graph.lock(&mut node);
    let sink_deadline = graph
        .get_sink_relative_deadline()
        .ok_or(DagError::MissingSinkDeadline(dag_id))?;

    let mut order = Vec::with_capacity(graph.node_count());
    depth_first_search(&*graph, graph.node_indices(), |event| match event {
        DfsEvent::Finish(idx, _) => {
            order.push(idx);
            Ok(())
        }
        DfsEvent::BackEdge(_, _) => Err(DagError::ContainsCycle(dag_id)),
        _ => Ok(()),
    })?;

    // Forward pass to compute earliest finish and critical path length
    let mut earliest_finish: Vec<Duration> = graph
        .node_references()
        .map(|(_, info)| info.wcet.unwrap_or(Duration::ZERO))
        .collect();
    let mut critical_path = Duration::ZERO;
    for &idx in order.iter().rev() {
        let mut start = Duration::ZERO;
        for pred in graph.neighbors_directed(idx, Direction::Incoming) {
            let pred_finish = earliest_finish[pred.index()]; // Safe: pred is a valid index
            start = start.max(pred_finish);
        }
        let finish = &mut earliest_finish[idx.index()]; // Safe: idx is a valid index
        *finish = start.checked_add(*finish).ok_or(DagError::InfeasibleWcet {
            dag_id,
            critical_path: None,
            deadline: sink_deadline,
        })?;
        critical_path = critical_path.max(*finish);
    }

    let invalid_path = || DagError::InfeasibleWcet {
        dag_id,
        critical_path: Some(critical_path),
        deadline: sink_deadline,
    };

    if critical_path > sink_deadline {
        return Err(invalid_path());
    }
    let critical_slack = sink_deadline - critical_path;

    // Backward pass to compute latest start times and timing estimates for each node
    // No overflow or node ID checks needed, as forward pass already ensures times are feasible
    let mut latest_start: Vec<Duration> = graph.node_references().map(|_| sink_deadline).collect();
    for idx in order {
        let mut latest_finish = sink_deadline;
        for successor in graph.neighbors_directed(idx, Direction::Outgoing) {
            let start = latest_start[successor.index()];
            latest_finish = latest_finish.min(start);
        }
        let info = graph.node_weight_mut(idx).unwrap();

        let estimated_wcet = info.wcet.unwrap_or(Duration::ZERO);
        let earliest_finish = earliest_finish[idx.index()];
        let earliest_start = earliest_finish - estimated_wcet;
        let slack = latest_finish - earliest_finish;

        latest_start[idx.index()] = latest_finish - estimated_wcet;
        info.timing = Some(TimingInfo {
            estimated_wcet,
            earliest_start,
            latest_finish,
            is_in_critical_path: slack == critical_slack,
        });
    }

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

                // [end] pubsub communication latency
                let end = awkernel_lib::time::Instant::now().uptime().as_nanos() as u64;
                record_subscribe_timestamp(period_index as usize, end, 1, dag_info.node_id.clone());

                if dag.has_stale_deadline(node_idx) {
                    crate::r#yield().await;
                }

                let results = f(args);
                publishers
                    .send_all_with_period_index(results, 1, period_index as usize, dag_info.node_id)
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

    let dag = get_dag(dag_info.dag_id).unwrap();
    let node_idx = to_node_index(dag_info.node_id);

    // Spawning wakes the source before its future is polled.
    let mut interval = interval(period, dag_info.dag_id);
    dag.set_next_release_time(interval.next_tick_target());

    // TODO(sykwer): Improve mechanisms to more closely align performance behavior with the DAG scheduling model.
    let future = async move {
        let publishers = <Ret as VectorToPublishers>::create_publishers(
            publish_topic_names,
            Attribute::default(),
        );

        // Consume the first tick here to start the loop's main body without an initial delay.
        interval.tick().await;

        loop {
            #[cfg(feature = "period-index-propagation")]
            {
                let index = get_period_index(dag_info.dag_id) as usize;
                if index != 0 {
                    // [start] cycle deviation index >= 1
                    let release_time =
                        awkernel_lib::time::Instant::now().uptime().as_nanos() as u64;
                    update_cycle_start_timestamp(index, release_time, dag_info.dag_id);
                }
                let results = f();
                publishers
                    .send_all_with_period_index(results, 0, index, dag_info.node_id)
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

            dag.set_next_release_time(interval.next_tick_target());
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

                // [end] pubsub communication latency
                let end = awkernel_lib::time::Instant::now().uptime().as_nanos() as u64;
                record_subscribe_timestamp(period_index as usize, end, 2, dag_info.node_id.clone());

                let timenow = awkernel_lib::time::Instant::now().uptime().as_nanos() as u64;
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

    /// Returns the estimates computed during DAG validation for a node ID from [`DagInfo`].
    /// Analysis is invalidated when the graph or its sink deadline changes.
    #[cfg(test)]
    fn timing_info(dag: &Dag, node_id: u32) -> Result<TimingInfo, DagError> {
        let mut node = MCSNode::new();
        let graph = dag.graph.lock(&mut node);
        let index = to_node_index(node_id);
        graph
            .node_weight(index)
            .ok_or(DagError::NodeNotFound(dag.id, index.index()))?
            .timing
            .ok_or(DagError::MissingNodeTiming(dag.id, index.index()))
    }

    #[test]
    fn late_node_keeps_the_deadline_of_its_job() {
        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &["deadline_test_topic".into()], None);
        let sink = dag.add_node_with_topic_edges(&["deadline_test_topic".into()], &[], None);
        dag.set_relative_deadline(sink, Duration::from_micros(50))
            .unwrap();

        // A non-source node does not release a job.
        assert_eq!(dag.get_or_release_job(sink, true).job, None);

        // The source node releases job 0. A later wake in job 0 keeps its timing information.
        dag.set_next_release_time(Instant::zero() + Duration::from_micros(10));
        let job_0 = JobInfo {
            release_time: 10,
            absolute_deadline: 60,
        };
        assert_eq!(dag.get_or_release_job(source, true).job, Some(job_0));
        assert_eq!(dag.get_or_release_job(source, true).job, Some(job_0));

        // The input of job 0 can reach the sink node without a wake.
        assert!(dag.has_stale_deadline(sink));

        dag.finish_job(source);

        // A preempted source node resumes before the next period and does not release job 1.
        assert_eq!(dag.get_or_release_job(source, false).job, None);
        dag.set_next_release_time(Instant::zero() + Duration::from_micros(20));
        let job_1 = JobInfo {
            release_time: 20,
            absolute_deadline: 70,
        };
        assert_eq!(dag.get_or_release_job(source, true).job, Some(job_1));

        // The sink node wakes for job 0 after the release of job 1.
        assert_eq!(dag.get_or_release_job(sink, true).job, Some(job_0));
        assert!(!dag.has_stale_deadline(sink));

        // The source node released job 1.
        dag.finish_job(sink);
        assert!(dag.has_stale_deadline(sink));
        assert_eq!(dag.get_or_release_job(sink, true).job, Some(job_1));
        assert!(!dag.has_stale_deadline(sink));
        assert!(!dag.jobs.lock(&mut MCSNode::new()).contains_key(&0));
    }

    #[test]
    fn deadline_stays_until_every_node_finishes_its_job() {
        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &["retention_test_a".into()], None);
        let middle = dag.add_node_with_topic_edges(
            &["retention_test_a".into()],
            &["retention_test_b".into()],
            None,
        );
        let sink = dag.add_node_with_topic_edges(&["retention_test_b".into()], &[], None);
        dag.set_relative_deadline(sink, Duration::from_micros(50))
            .unwrap();

        // The source node releases jobs 0, 1, and 2.
        dag.set_next_release_time(Instant::zero() + Duration::from_micros(10));
        assert_eq!(
            dag.get_or_release_job(source, true).job,
            Some(JobInfo {
                release_time: 10,
                absolute_deadline: 60,
            })
        );
        dag.finish_job(source);
        dag.set_next_release_time(Instant::zero() + Duration::from_micros(20));
        assert_eq!(
            dag.get_or_release_job(source, true).job,
            Some(JobInfo {
                release_time: 20,
                absolute_deadline: 70,
            })
        );
        dag.finish_job(source);
        dag.set_next_release_time(Instant::zero() + Duration::from_micros(30));
        assert_eq!(
            dag.get_or_release_job(source, true).job,
            Some(JobInfo {
                release_time: 30,
                absolute_deadline: 80,
            })
        );

        // The sink node finishes job 0 before the middle node records its finish.
        dag.finish_job(sink);
        assert_eq!(
            dag.get_or_release_job(middle, true).job,
            Some(JobInfo {
                release_time: 10,
                absolute_deadline: 60,
            })
        );

        dag.finish_job(middle);
        assert_eq!(
            dag.get_or_release_job(middle, true).job,
            Some(JobInfo {
                release_time: 20,
                absolute_deadline: 70,
            })
        );
        assert_eq!(
            dag.get_or_release_job(sink, true).job,
            Some(JobInfo {
                release_time: 20,
                absolute_deadline: 70,
            })
        );

        let mut node = MCSNode::new();
        let jobs: Vec<u64> = dag.jobs.lock(&mut node).keys().copied().collect();
        assert_eq!(jobs, [1, 2]);
    }

    #[test]
    fn deadlines_of_a_stopped_node_are_capped() {
        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &["cap_test_topic".into()], None);
        let sink = dag.add_node_with_topic_edges(&["cap_test_topic".into()], &[], None);
        dag.set_relative_deadline(sink, Duration::from_micros(50))
            .unwrap();

        // The sink node stopped, for example by a panic, and the source node keeps releasing.
        for release_time in 0..100 {
            dag.set_next_release_time(Instant::zero() + Duration::from_micros(release_time));
            dag.get_or_release_job(source, true);
            dag.finish_job(source);
        }

        let mut node = MCSNode::new();
        let jobs = dag.jobs.lock(&mut node);
        // The cap for two nodes.
        assert_eq!(jobs.len(), 2 * (Attribute::default().queue_size + 1) + 1);
        assert_eq!(
            jobs.last_key_value(),
            Some((
                &99,
                &JobInfo {
                    release_time: 99,
                    absolute_deadline: 149,
                }
            ))
        );
    }

    #[test]
    fn sink_deadline_reports_missing_deadlines_and_nodes() {
        let dag = create_dag();
        assert!(matches!(
            dag.get_sink_relative_deadline(),
            Err(DagError::MissingSinkDeadline(id)) if id == dag.id
        ));

        let sink = dag.add_node_with_topic_edges(&[], &[], None);
        assert!(matches!(
            dag.get_sink_relative_deadline(),
            Err(DagError::MissingSinkDeadline(id)) if id == dag.id
        ));
        let missing = NodeIndex::new(sink.index() + 1);
        assert!(matches!(
            dag.set_relative_deadline(missing, Duration::from_micros(50)),
            Err(DagError::NodeNotFound(id, node)) if id == dag.id && node == missing.index()
        ));
        dag.set_relative_deadline(sink, Duration::from_micros(50))
            .unwrap();
        assert_eq!(
            dag.get_sink_relative_deadline().unwrap(),
            Duration::from_micros(50)
        );
    }

    #[test]
    fn dag_deadline_uses_job_release_time() {
        use crate::task::{DagInfo, State};

        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &["dag_deadline_test_topic".into()], None);
        let sink = dag.add_node_with_topic_edges(&["dag_deadline_test_topic".into()], &[], None);
        dag.set_relative_deadline(sink, Duration::from_micros(50))
            .unwrap();
        let source_info = DagInfo {
            dag_id: dag.id,
            node_id: source.index() as u32,
        };
        let sink_info = DagInfo {
            dag_id: dag.id,
            node_id: sink.index() as u32,
        };

        assert_eq!(
            calculate_and_update_dag_deadline(&sink_info, 5, State::Waiting),
            55
        );
        // Timer latency must not postpone job 0's deadline. Truncate sub-microsecond time.
        dag.set_next_release_time(Instant::zero() + Duration::from_nanos(10_999));
        assert_eq!(
            calculate_and_update_dag_deadline(&source_info, 13, State::Waiting),
            60
        );
        assert_eq!(
            calculate_and_update_dag_deadline(&source_info, 14, State::Preempted),
            60
        );
        dag.finish_job(source);
        dag.set_next_release_time(Instant::zero() + Duration::from_micros(20));
        assert_eq!(
            calculate_and_update_dag_deadline(&source_info, 15, State::Preempted),
            65
        );
        assert!(!dag.jobs.lock(&mut MCSNode::new()).contains_key(&1));

        // An overrun can leave the next Burst job overdue even before its source wakes.
        assert_eq!(
            calculate_and_update_dag_deadline(&source_info, 85, State::Waiting),
            70
        );
        dag.finish_job(source);
        dag.set_next_release_time(Instant::zero() + Duration::from_micros(30));
        assert_eq!(
            calculate_and_update_dag_deadline(&source_info, 86, State::Waiting),
            80
        );
        assert_eq!(
            calculate_and_update_dag_deadline(&sink_info, 87, State::Waiting),
            60
        );
        dag.finish_job(sink);
        assert_eq!(
            calculate_and_update_dag_deadline(&sink_info, 88, State::Waiting),
            70
        );
        dag.finish_job(sink);
        assert_eq!(
            calculate_and_update_dag_deadline(&sink_info, 89, State::Waiting),
            80
        );
    }

    #[test]
    fn dag_deadline_is_fixed_when_job_is_released() {
        use crate::task::{DagInfo, State};

        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &["fixed_deadline_topic".into()], None);
        let sink = dag.add_node_with_topic_edges(&["fixed_deadline_topic".into()], &[], None);
        dag.set_relative_deadline(sink, Duration::from_micros(50))
            .unwrap();
        let source_info = DagInfo {
            dag_id: dag.id,
            node_id: source.index() as u32,
        };
        let sink_info = DagInfo {
            dag_id: dag.id,
            node_id: sink.index() as u32,
        };

        dag.set_next_release_time(Instant::zero() + Duration::from_micros(10));
        assert_eq!(
            calculate_and_update_dag_deadline(&source_info, 11, State::Waiting),
            60
        );

        dag.set_relative_deadline(sink, Duration::from_micros(100))
            .unwrap();
        assert_eq!(
            calculate_and_update_dag_deadline(&source_info, 12, State::Waiting),
            60
        );
        assert_eq!(
            calculate_and_update_dag_deadline(&sink_info, 13, State::Waiting),
            60
        );

        dag.finish_job(source);
        dag.set_next_release_time(Instant::zero() + Duration::from_micros(20));
        assert_eq!(
            calculate_and_update_dag_deadline(&source_info, 21, State::Waiting),
            120
        );

        dag.finish_job(sink);
        assert_eq!(
            calculate_and_update_dag_deadline(&sink_info, 22, State::Waiting),
            120
        );
    }

    #[test]
    #[should_panic(expected = "The DAG source released a job before its next release time was set")]
    fn source_release_requires_tick_target() {
        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &[], None);
        dag.get_or_release_job(source, true);
    }

    fn timing_chain(wcets: [Option<Duration>; 3]) -> (Arc<Dag>, [NodeIndex; 3]) {
        let dag = create_dag();
        let source_topic: Cow<'static, str> = alloc::format!("timing_{}_source", dag.id).into();
        let sink_topic: Cow<'static, str> = alloc::format!("timing_{}_sink", dag.id).into();
        let source =
            dag.add_node_with_topic_edges(&[], core::slice::from_ref(&source_topic), wcets[0]);
        let middle = dag.add_node_with_topic_edges(
            core::slice::from_ref(&source_topic),
            core::slice::from_ref(&sink_topic),
            wcets[1],
        );
        let sink = dag.add_node_with_topic_edges(&[sink_topic], &[], wcets[2]);
        dag.set_relative_deadline(sink, Duration::from_millis(100))
            .unwrap();
        (dag, [source, middle, sink])
    }

    #[test]
    fn latest_finish_priority_tracks_each_released_job_and_keeps_real_deadline() {
        let ms = Duration::from_millis;
        let (dag, [source, middle, sink]) =
            timing_chain([Some(ms(10)), Some(ms(20)), Some(ms(30))]);
        compute_timing(&dag).unwrap();
        let info = |index: NodeIndex| DagInfo {
            dag_id: dag.id,
            node_id: u32::try_from(index.index()).unwrap(),
        };
        let source_info = info(source);
        let middle_info = info(middle);
        let sink_info = info(sink);

        // Before release, the real deadline also supplies the ordering key.
        assert_eq!(
            calculate_dag_latest_finish_priority(&middle_info, 5, State::Waiting),
            (100_005, 100_005)
        );
        dag.set_next_release_time(Instant::zero() + Duration::from_micros(1_000));
        assert_eq!(
            calculate_dag_latest_finish_priority(&source_info, 1_100, State::Waiting),
            (101_000, 51_000)
        );
        assert_eq!(
            calculate_dag_latest_finish_priority(&middle_info, 1_200, State::Waiting),
            (101_000, 71_000)
        );
        assert_eq!(
            calculate_dag_latest_finish_priority(&sink_info, 1_300, State::Waiting),
            (101_000, 101_000)
        );
        assert_eq!(
            calculate_dag_latest_finish_priority(&source_info, 1_400, State::Preempted),
            (101_000, 51_000)
        );

        dag.finish_job(source);
        dag.set_next_release_time(Instant::zero() + Duration::from_micros(2_000));
        assert_eq!(
            calculate_dag_latest_finish_priority(&source_info, 2_100, State::Waiting),
            (102_000, 52_000)
        );
        // The middle node is still processing the earlier job.
        assert_eq!(
            calculate_dag_latest_finish_priority(&middle_info, 2_200, State::Waiting),
            (101_000, 71_000)
        );
        dag.set_relative_deadline(sink, ms(120)).unwrap();
        assert_eq!(
            calculate_dag_latest_finish_priority(&middle_info, 2_300, State::Waiting),
            (101_000, 101_000)
        );
    }

    #[test]
    fn release_after_unreleased_snapshot_keeps_deadline_stale_until_next_wake() {
        let ms = Duration::from_millis;
        let (dag, [source, middle, _]) = timing_chain([Some(ms(10)), Some(ms(20)), Some(ms(30))]);
        compute_timing(&dag).unwrap();
        let info = |index: NodeIndex| DagInfo {
            dag_id: dag.id,
            node_id: u32::try_from(index.index()).unwrap(),
        };
        let middle_info = info(middle);

        // Release the source between the snapshot and its priority projection.
        let snapshot = dag_job_timing(&middle_info, State::Waiting);
        assert!(snapshot.job.is_none());
        dag.set_next_release_time(Instant::zero() + Duration::from_micros(1_000));
        assert_eq!(
            calculate_and_update_dag_deadline(&info(source), 1_100, State::Waiting),
            101_000
        );
        assert_eq!(
            snapshot.latest_finish_priority(dag.id, 5),
            (100_005, 100_005)
        );
        assert!(dag.has_stale_deadline(middle));
        assert_eq!(
            calculate_dag_latest_finish_priority(&middle_info, 1_200, State::Waiting),
            (101_000, 71_000)
        );
        assert!(!dag.has_stale_deadline(middle));
    }

    fn timing_diamond(wcets: [Option<Duration>; 4]) -> (Arc<Dag>, [NodeIndex; 4]) {
        let dag = create_dag();
        let source_to_a: Cow<'static, str> = alloc::format!("timing_{}_source_a", dag.id).into();
        let source_to_b: Cow<'static, str> = alloc::format!("timing_{}_source_b", dag.id).into();
        let a_to_sink: Cow<'static, str> = alloc::format!("timing_{}_a_sink", dag.id).into();
        let b_to_sink: Cow<'static, str> = alloc::format!("timing_{}_b_sink", dag.id).into();
        let source = dag.add_node_with_topic_edges(
            &[],
            &[source_to_a.clone(), source_to_b.clone()],
            wcets[0],
        );
        let a = dag.add_node_with_topic_edges(
            core::slice::from_ref(&source_to_a),
            core::slice::from_ref(&a_to_sink),
            wcets[1],
        );
        let b = dag.add_node_with_topic_edges(
            core::slice::from_ref(&source_to_b),
            core::slice::from_ref(&b_to_sink),
            wcets[2],
        );
        let sink = dag.add_node_with_topic_edges(&[a_to_sink, b_to_sink], &[], wcets[3]);
        dag.set_relative_deadline(sink, Duration::from_millis(100))
            .unwrap();
        (dag, [source, a, b, sink])
    }

    #[test]
    fn chain_wcets_below_deadline_are_feasible() {
        let (dag, _) = timing_chain([
            Some(Duration::from_millis(10)),
            Some(Duration::from_millis(20)),
            Some(Duration::from_millis(30)),
        ]);

        assert!(compute_timing(&dag).is_ok());
    }

    #[test]
    fn timing_uses_node_indices_when_registration_order_is_reversed() {
        let dag = create_dag();
        let source_topic: Cow<'static, str> =
            alloc::format!("reverse_timing_{}_source", dag.id).into();
        let sink_topic: Cow<'static, str> = alloc::format!("reverse_timing_{}_sink", dag.id).into();
        let sink = dag.add_node_with_topic_edges(
            core::slice::from_ref(&sink_topic),
            &[],
            Some(Duration::from_millis(30)),
        );
        let middle = dag.add_node_with_topic_edges(
            core::slice::from_ref(&source_topic),
            core::slice::from_ref(&sink_topic),
            Some(Duration::from_millis(20)),
        );
        let source =
            dag.add_node_with_topic_edges(&[], &[source_topic], Some(Duration::from_millis(10)));
        dag.set_relative_deadline(sink, Duration::from_millis(60))
            .unwrap();

        compute_timing(&dag).unwrap();
        let timing =
            |idx: NodeIndex| timing_info(&dag, u32::try_from(idx.index()).unwrap()).unwrap();
        assert_eq!(timing(source).earliest_start(), Duration::ZERO);
        assert_eq!(timing(middle).earliest_finish(), Duration::from_millis(30));
        assert_eq!(timing(middle).latest_finish(), Duration::from_millis(30));
        assert_eq!(timing(sink).latest_finish(), Duration::from_millis(60));

        dag.set_relative_deadline(sink, Duration::from_millis(59))
            .unwrap();
        assert!(matches!(
            compute_timing(&dag),
            Err(DagError::InfeasibleWcet {
                dag_id: id,
                critical_path: Some(path),
                deadline,
            }) if id == dag.id
                && path == Duration::from_millis(60)
                && deadline == Duration::from_millis(59)
        ));
    }

    #[test]
    fn branch_join_feasibility_uses_the_longest_path_not_the_sum_of_branches() {
        let (dag, [_, _, _, sink]) = timing_diamond([
            Some(Duration::from_millis(10)),
            Some(Duration::from_millis(60)),
            Some(Duration::from_millis(30)),
            Some(Duration::from_millis(20)),
        ]);

        // The longest path is 90 ms, although the sum of all WCETs is 120 ms.
        assert!(compute_timing(&dag).is_ok());
        dag.set_relative_deadline(sink, Duration::from_millis(89))
            .unwrap();
        assert!(matches!(
            compute_timing(&dag),
            Err(DagError::InfeasibleWcet {
                dag_id: id,
                critical_path: Some(path),
                deadline,
            }) if id == dag.id
                && path == Duration::from_millis(90)
                && deadline == Duration::from_millis(89)
        ));
    }

    #[test]
    fn critical_path_equal_to_deadline_is_feasible() {
        let (dag, [_, _, sink]) = timing_chain([
            Some(Duration::from_millis(10)),
            Some(Duration::from_millis(20)),
            Some(Duration::from_millis(30)),
        ]);
        dag.set_relative_deadline(sink, Duration::from_millis(60))
            .unwrap();

        assert!(compute_timing(&dag).is_ok());
    }

    #[test]
    fn chain_path_over_deadline_returns_infeasible_wcet() {
        let (dag, _) = timing_chain([
            Some(Duration::from_millis(50)),
            Some(Duration::from_millis(40)),
            Some(Duration::from_millis(30)),
        ]);
        let error = compute_timing(&dag).unwrap_err();
        assert!(matches!(
            error,
            DagError::InfeasibleWcet{dag_id: id, critical_path: Some(path), deadline}
                if id == dag.id
                    && path == Duration::from_millis(120)
                    && deadline == Duration::from_millis(100)
        ));
        assert_eq!(
            alloc::format!("{error}"),
            alloc::format!(
                "DAG#{}: estimated critical path 120ms exceeds sink relative deadline 100ms",
                dag.id
            )
        );
    }

    #[test]
    fn diamond_path_over_deadline_returns_infeasible_wcet() {
        let (dag, _) = timing_diamond([
            Some(Duration::from_millis(50)),
            Some(Duration::from_millis(40)),
            Some(Duration::from_millis(5)),
            Some(Duration::from_millis(30)),
        ]);
        // The long branch takes 120 ms, while the other branch fits in 85 ms.
        assert!(matches!(
            compute_timing(&dag),
            Err(DagError::InfeasibleWcet{dag_id: id, critical_path: Some(path), deadline})
                if id == dag.id
                    && path == Duration::from_millis(120)
                    && deadline == Duration::from_millis(100)
        ));
    }

    #[test]
    fn public_registration_validates_the_combined_wcet_of_all_reactor_types() {
        use futures::FutureExt;

        let dag = create_dag();
        let source_topic: Cow<'static, str> =
            alloc::format!("registered_timing_{}_source", dag.id).into();
        let sink_topic: Cow<'static, str> =
            alloc::format!("registered_timing_{}_sink", dag.id).into();

        async {
            dag.register_periodic_reactor::<_, (u32,)>(
                "timing_source".into(),
                || (1,),
                alloc::vec![source_topic.clone()],
                SchedulerType::PrioritizedFIFO(0),
                Duration::from_millis(100),
                Some(Duration::from_millis(50)),
            )
            .await;
            dag.register_reactor::<_, (u32,), (u32,)>(
                "timing_middle".into(),
                |value| value,
                alloc::vec![source_topic],
                alloc::vec![sink_topic.clone()],
                SchedulerType::PrioritizedFIFO(0),
                Some(Duration::from_millis(40)),
            )
            .await;
            dag.register_sink_reactor::<_, (u32,)>(
                "timing_sink".into(),
                |_| {},
                alloc::vec![sink_topic],
                SchedulerType::PrioritizedFIFO(0),
                Duration::from_millis(100),
                Some(Duration::from_millis(30)),
            )
            .await;
        }
        .now_or_never()
        .expect("registration must complete without spawning or waiting for reactors");

        let result = validate_all_rules(core::slice::from_ref(&dag));
        remove_dag(dag.id);

        // Dropping any one registration's WCET would make this 120 ms chain feasible.
        let errors = result.unwrap_err();
        assert!(matches!(
            errors.as_slice(),
            [DagError::InfeasibleWcet{dag_id: id, critical_path: Some(path), deadline}]
                if *id == dag.id
                    && *path == Duration::from_millis(120)
                    && *deadline == Duration::from_millis(100)
        ));
    }

    #[test]
    fn timing_overflow_returns_infeasible_wcet() {
        let (dag, [_, _, sink]) =
            timing_chain([Some(Duration::MAX), Some(Duration::from_nanos(1)), None]);
        dag.set_relative_deadline(sink, Duration::MAX).unwrap();

        let error = compute_timing(&dag).unwrap_err();
        assert!(matches!(
            error,
            DagError::InfeasibleWcet{dag_id: id, critical_path: None, deadline: Duration::MAX} if id == dag.id
        ));
        assert_eq!(
            alloc::format!("{error}"),
            alloc::format!(
                "DAG#{}: estimated critical path exceeds Duration::MAX (sink relative deadline {:?})",
                dag.id,
                Duration::MAX
            )
        );
    }

    #[test]
    fn sink_wcet_over_deadline_returns_infeasible_wcet() {
        let (dag, _) = timing_chain([None, None, Some(Duration::from_millis(101))]);
        assert!(matches!(
            compute_timing(&dag),
            Err(DagError::InfeasibleWcet{dag_id: id, critical_path: Some(path), deadline})
                if id == dag.id
                    && path == Duration::from_millis(101)
                    && deadline == Duration::from_millis(100)
        ));
    }

    #[test]
    fn sink_wcet_is_included_when_the_critical_path_overflows() {
        let (dag, [_, _, sink]) =
            timing_chain([Some(Duration::MAX), None, Some(Duration::from_nanos(1))]);
        dag.set_relative_deadline(sink, Duration::MAX).unwrap();

        assert!(matches!(
            compute_timing(&dag),
            Err(DagError::InfeasibleWcet{dag_id: id, critical_path: None, deadline: Duration::MAX}) if id == dag.id
        ));
    }

    #[test]
    fn maximum_duration_critical_path_is_feasible() {
        let (dag, [_, _, sink]) = timing_chain([Some(Duration::MAX), None, None]);
        dag.set_relative_deadline(sink, Duration::MAX).unwrap();

        assert!(compute_timing(&dag).is_ok());
    }

    #[test]
    fn zero_wcets_fit_a_zero_relative_deadline() {
        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &[], None);
        dag.set_relative_deadline(source, Duration::ZERO).unwrap();

        assert!(compute_timing(&dag).is_ok());
    }

    #[test]
    fn timing_without_sink_deadline_returns_missing_sink_deadline() {
        let dag = create_dag();
        dag.add_node_with_topic_edges(&[], &[], None);

        assert!(matches!(
            compute_timing(&dag),
            Err(DagError::MissingSinkDeadline(id)) if id == dag.id
        ));
    }

    #[test]
    fn absent_and_zero_wcets_remain_distinct_but_analyze_as_zero() {
        let (dag, [absent, zero, sink]) = timing_chain([None, Some(Duration::ZERO), None]);
        dag.set_relative_deadline(sink, Duration::ZERO).unwrap();

        compute_timing(&dag).unwrap();
        let mut node = MCSNode::new();
        let graph = dag.graph.lock(&mut node);
        assert_eq!(graph.node_weight(absent).unwrap().wcet, None);
        assert_eq!(graph.node_weight(zero).unwrap().wcet, Some(Duration::ZERO));
    }

    #[test]
    fn timing_estimates_identify_critical_and_short_branches() {
        let ms = Duration::from_millis;
        let (dag, [source, long, short, sink]) =
            timing_diamond([Some(ms(10)), Some(ms(60)), Some(ms(30)), Some(ms(20))]);
        compute_timing(&dag).unwrap();
        let info = |idx: NodeIndex| timing_info(&dag, u32::try_from(idx.index()).unwrap()).unwrap();

        let long = info(long);
        assert_eq!(
            (long.earliest_start(), long.earliest_finish()),
            (ms(10), ms(70))
        );
        assert_eq!(
            (long.latest_start(), long.latest_finish()),
            (ms(20), ms(80))
        );
        assert_eq!(long.slack(), ms(10));
        assert!(long.is_in_critical_path());

        let short = info(short);
        assert_eq!(
            (short.earliest_start(), short.earliest_finish()),
            (ms(10), ms(40))
        );
        assert_eq!(
            (short.latest_start(), short.latest_finish()),
            (ms(50), ms(80))
        );
        assert_eq!(short.slack(), ms(40));
        assert!(!short.is_in_critical_path());
        assert!(info(source).is_in_critical_path());
        assert!(info(sink).is_in_critical_path());
    }

    #[test]
    fn equal_critical_paths_and_missing_wcet_are_preserved() {
        let ms = Duration::from_millis;
        let (dag, [_, a, b, sink]) =
            timing_diamond([None, Some(ms(20)), Some(ms(20)), Some(Duration::ZERO)]);
        compute_timing(&dag).unwrap();
        let info = |idx: NodeIndex| timing_info(&dag, u32::try_from(idx.index()).unwrap()).unwrap();
        assert!(info(a).is_in_critical_path());
        assert!(info(b).is_in_critical_path());
        assert_eq!(info(sink).estimated_wcet(), Duration::ZERO);
        let source = dag.get_source_nodes()[0];
        assert_eq!(info(source).estimated_wcet(), Duration::ZERO);
        assert_eq!(info(source).earliest_start(), Duration::ZERO);
        assert_eq!(info(source).earliest_finish(), Duration::ZERO);
    }

    #[test]
    fn changed_deadline_invalidates_previously_computed_timing() {
        let (dag, [source, _, sink]) = timing_chain([None, None, None]);
        compute_timing(&dag).unwrap();
        dag.set_relative_deadline(sink, Duration::ZERO).unwrap();
        assert!(matches!(
            timing_info(&dag, u32::try_from(source.index()).unwrap()),
            Err(DagError::MissingNodeTiming(_, _))
        ));
    }

    #[cfg(feature = "std")]
    #[test]
    fn invalidating_timing_warns_once_for_each_analyzed_dag() {
        struct TestLogger(std::sync::Mutex<Vec<alloc::string::String>>);

        impl log::Log for TestLogger {
            fn enabled(&self, metadata: &log::Metadata<'_>) -> bool {
                metadata.level() == log::Level::Warn
            }

            fn log(&self, record: &log::Record<'_>) {
                if self.enabled(record.metadata()) {
                    self.0
                        .lock()
                        .unwrap()
                        .push(alloc::format!("{}", record.args()));
                }
            }

            fn flush(&self) {}
        }

        static LOGGER: TestLogger = TestLogger(std::sync::Mutex::new(Vec::new()));
        log::set_logger(&LOGGER).unwrap();
        log::set_max_level(log::LevelFilter::Warn);

        let (registered_dag, _) = timing_chain([None, None, None]);
        let registration_id = alloc::format!("DAG#{} ", registered_dag.id);
        assert!(!LOGGER
            .0
            .lock()
            .unwrap()
            .iter()
            .any(|message| message.starts_with(&registration_id)));
        compute_timing(&registered_dag).unwrap();
        registered_dag.add_node_with_topic_edges(&[], &[], None);
        registered_dag.add_node_with_topic_edges(&[], &[], None);

        let (deadline_dag, [_, _, sink]) = timing_chain([None, None, None]);
        let deadline_id = alloc::format!("DAG#{} ", deadline_dag.id);
        compute_timing(&deadline_dag).unwrap();
        deadline_dag
            .set_relative_deadline(sink, Duration::ZERO)
            .unwrap();
        deadline_dag
            .set_relative_deadline(sink, Duration::ZERO)
            .unwrap();

        let messages = LOGGER.0.lock().unwrap();
        let registration_warnings: Vec<_> = messages
            .iter()
            .filter(|message| message.starts_with(&registration_id))
            .collect();
        assert_eq!(registration_warnings.len(), 1);
        assert!(registration_warnings[0].contains("node registration"));
        assert!(registration_warnings[0].contains("LLFT wakes will use real deadlines"));
        let deadline_warnings: Vec<_> = messages
            .iter()
            .filter(|message| message.starts_with(&deadline_id))
            .collect();
        assert_eq!(deadline_warnings.len(), 1);
        assert!(deadline_warnings[0].contains("deadline change"));
    }
}
