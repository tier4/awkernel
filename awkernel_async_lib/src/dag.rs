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
//! - `set_node_wcet()`: Method to set the estimated Worst-Case Execution Time (WCET) for a node.
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
//! # Estimated WCET and Node Deadlines
//!
//! Each node has an estimated WCET, which is zero unless set with `set_node_wcet()`.
//! The `register_xx_reactor()` methods return the `NodeIndex` of the new node for this purpose.
//! The `finish_create_dags()` method computes the latest finish of each node  as an offset from
//! the job release, and checks that the WCETs fit. The latest finish of the sink is its relative deadline `D`,
//! and that of any other node is the minimum over its successors of `latest finish - WCET`.
//!
//! - **`SchedulerType::REDF`** gives a node the deadline `release time + latest finish`.
//! - **GEDF and ClusteredEDF** ignore the WCETs and give every node of a job the deadline `release time + D`.
//!
//! - **Feasible WCETs**: The critical path, which is the sum of the WCETs along the longest path, must not exceed `D`.
//!   Otherwise `finish_create_dags` returns `DagError::InfeasibleWcet`.
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
    scheduler::SchedulerType, task::DagInfo, time_interval::interval, Attribute, MultipleReceiver,
    MultipleSender, VectorToPublishers, VectorToSubscribers,
};
use graph::{
    algo::{connected_components, is_cyclic_directed},
    direction::Direction,
};
use visit::{EdgeRef, IntoNodeReferences, NodeRef};

pub use graph::NodeIndex;

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
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::{future::Future, pin::Pin, time::Duration};

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
    MissingSinkDeadline(u32),
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
    WcetOverflow(u32),
    InfeasibleWcet(u32, usize),
}

#[rustfmt::skip]
impl core::fmt::Display for DagError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DagError::NodeNotFound(dag_id, node_id) => write!(f, "DAG#{dag_id} Node#{node_id} not found"),
            DagError::MissingSinkDeadline(dag_id) => write!(f, "DAG#{dag_id} has no sink relative deadline"),
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
            DagError::WcetOverflow(dag_id) => write!(f, "DAG#{dag_id}: estimated WCET computation overflowed"),
            DagError::InfeasibleWcet(dag_id, node_id) => {
                write!(f, "DAG#{dag_id} Node#{node_id}: estimated WCETs exceed the sink relative deadline")
            }
        }
    }
}

type DagGraph = graph::Graph<NodeInfo, EdgeInfo>;

impl DagGraph {
    #[inline]
    fn get_node_wcet(&self, node_idx: NodeIndex) -> Option<Duration> {
        self.node_weight(node_idx)
            .map(|info| info.timing.estimated_wcet)
    }

    #[inline]
    fn set_node_wcet(&mut self, node_idx: NodeIndex, wcet: Duration) -> bool {
        match self.node_weight_mut(node_idx) {
            Some(info) => {
                info.timing.estimated_wcet = wcet;
                true
            }
            None => false,
        }
    }

    #[inline]
    fn get_sink_relative_deadline(&self) -> Option<Duration> {
        let sink_node_index = self.externals(Direction::Outgoing).next()?;
        self.node_weight(sink_node_index).unwrap().relative_deadline
    }

    #[inline]
    fn set_relative_deadline(&mut self, node_idx: NodeIndex, deadline: Duration) -> bool {
        match self.node_weight_mut(node_idx) {
            Some(info) => {
                info.relative_deadline = Some(deadline);
                true
            }
            None => false,
        }
    }

    /// Returns the nodes in topological order: every node comes after all its predecessors.
    /// It uses Kahn's algorithm and runs in O(|V| + |E|) time.
    ///
    /// On a graph with a cycle, the nodes of the cycle, and the nodes reachable only through
    /// it, are missing from the result. Check `is_cyclic_directed` first, or compare the length
    /// with `node_count()`.
    fn topological_order(&self) -> Vec<NodeIndex> {
        let mut in_degree: BTreeMap<NodeIndex, usize> = self
            .node_indices()
            .map(|idx| {
                (
                    idx,
                    self.neighbors_directed(idx, Direction::Incoming).count(),
                )
            })
            .collect();
        let mut ready: Vec<NodeIndex> = in_degree
            .iter()
            .filter(|(_, degree)| **degree == 0)
            .map(|(idx, _)| *idx)
            .collect();
        let mut order: Vec<NodeIndex> = Vec::with_capacity(in_degree.len());
        while let Some(idx) = ready.pop() {
            order.push(idx);
            for succ in self.neighbors_directed(idx, Direction::Outgoing) {
                if let Some(degree) = in_degree.get_mut(&succ) {
                    *degree = degree.saturating_sub(1);
                    if *degree == 0 {
                        ready.push(succ);
                    }
                }
            }
        }
        order
    }
}

pub struct Dag {
    id: u32,
    graph: Mutex<DagGraph>,

    /// Release time of each released job that a node has not finished, keyed by job number.
    /// A job is one run of the DAG. It starts when the source node wakes for a new release.
    /// The absolute deadline of a node is the release time plus its `relative_deadline`.
    release_times: Mutex<BTreeMap<u64, u64>>,

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
        match graph.set_relative_deadline(node_idx, deadline) {
            true => Ok(()),
            false => Err(DagError::NodeNotFound(self.id, node_idx.index())),
        }
    }

    pub fn get_node_wcet(&self, node_idx: NodeIndex) -> Result<Duration, DagError> {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        graph
            .get_node_wcet(node_idx)
            .ok_or(DagError::NodeNotFound(self.id, node_idx.index()))
    }

    /// Sets the estimated WCET of a node. It is zero unless set.
    /// Call it before `finish_create_dags`, which derives the node deadlines from it.
    pub fn set_node_wcet(&self, node_idx: NodeIndex, wcet: Duration) -> Result<(), DagError> {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        match graph.set_node_wcet(node_idx, wcet) {
            true => Ok(()),
            false => Err(DagError::NodeNotFound(self.id, node_idx.index())),
        }
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
            timing: NodeTiming::default(),
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
    ) -> NodeIndex
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
                        DagInfo { dag_id, node_id },
                    )
                    .await
                })
            }));

        node_idx
    }

    pub async fn register_periodic_reactor<F, Ret>(
        &self,
        reactor_name: Cow<'static, str>,
        f: F,
        publish_topic_names: Vec<Cow<'static, str>>,
        sched_type: SchedulerType,
        period: Duration,
    ) -> NodeIndex
    where
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
                        DagInfo { dag_id, node_id },
                    )
                    .await
                })
            }),
        );

        node_idx
    }

    pub async fn register_sink_reactor<F, Args>(
        &self,
        reactor_name: Cow<'static, str>,
        f: F,
        subscribe_topic_names: Vec<Cow<'static, str>>,
        sched_type: SchedulerType,
        relative_deadline: Duration,
    ) -> NodeIndex
    where
        F: Fn(<Args::Subscribers as MultipleReceiver>::Item) + Send + 'static,
        Args: VectorToSubscribers,
        Args::Subscribers: Send,
        <Args::Subscribers as MultipleReceiver>::Item: TupleSize,
    {
        let node_idx = self.add_node_with_topic_edges(&subscribe_topic_names, &Vec::new());
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

        node_idx
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

    /// Returns the release time of the job that the node at `node_idx` processes next, and the
    /// result of `read_timing`, which gets the timing parameters of the node. The caller takes
    /// only the parameters it needs, with no copy of the others.
    /// If that job is not released and `release` is true, the source node releases it with
    /// the value of `release_time`. Any other wake uses that value without a release.
    ///
    /// `read_timing` runs while the DAG locks are held, so it must be short and must not use
    /// the DAG.
    pub(crate) fn get_or_release_job<R>(
        &self,
        node_idx: NodeIndex,
        release: bool,
        release_time: impl FnOnce() -> u64,
        read_timing: impl FnOnce(&NodeTiming) -> R,
    ) -> (u64, R) {
        let mut node = MCSNode::new();
        let mut release_times = self.release_times.lock(&mut node);

        let (job, release, read) = {
            let mut graph_node = MCSNode::new();
            let mut graph = self.graph.lock(&mut graph_node);
            let is_source = graph
                .neighbors_directed(node_idx, Direction::Incoming)
                .next()
                .is_none();
            let node_info = graph.node_weight_mut(node_idx).unwrap();
            let job = node_info.num_finished;
            let release = release && is_source;
            node_info.deadline_job = (release || release_times.contains_key(&job)).then_some(job);
            (job, release, read_timing(&node_info.timing))
        };

        let release_time = match release_times.get(&job) {
            Some(&released) => released,
            None => {
                let new_release_time = release_time();
                if release {
                    release_times.insert(job, new_release_time);
                }
                new_release_time
            }
        };

        (release_time, read)
    }

    /// Returns true if the job that the node at `node_idx` processes is released, but the
    /// last wake of the node did not get its deadline. This occurs if `recv_all` finds the input
    /// in the queue and returns without `wake_task`. A yield then gives the node the deadline.
    fn has_stale_deadline(&self, node_idx: NodeIndex) -> bool {
        let mut node = MCSNode::new();
        let release_times = self.release_times.lock(&mut node);

        let mut graph_node = MCSNode::new();
        let graph = self.graph.lock(&mut graph_node);
        let node_info = graph.node_weight(node_idx).unwrap();
        node_info.deadline_job != Some(node_info.num_finished)
            && release_times.contains_key(&node_info.num_finished)
    }

    /// Records that the node at `node_idx` finished its current job.
    fn finish_job(&self, node_idx: NodeIndex) {
        let mut node = MCSNode::new();
        let mut release_times = self.release_times.lock(&mut node);

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
        release_times.retain(|&job, _| job >= oldest_unfinished);

        // A node whose task ended, for example by a panic, stops counting. Flow control keeps
        // every running node at most `queue_size + 1` jobs behind its upstream node, so an
        // entry beyond this cap belongs only to such a node.
        let max_unfinished = graph.node_count() * (Attribute::default().queue_size + 1) + 1;
        while release_times.len() > max_unfinished {
            release_times.pop_first();
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

/// The timing parameters of a node. All are offsets from the release of the job.
#[derive(Clone, Copy, Debug, Default)]
pub struct NodeTiming {
    /// Estimated worst-case execution time of the node. It is zero unless set with `set_node_wcet()`.
    pub estimated_wcet: Duration,
    /// Estimated earliest start of the node, computed from the predecessors.
    pub estimated_earliest_start: Duration,
    /// Estimated latest finish of the node, computed from the successors.
    pub estimated_latest_finish: Duration,
    /// True if the node is on a critical path, that is, a longest path of the DAG by WCET.
    /// Such a node has the least slack, which is `D` minus the length of that path.
    pub is_critical: bool,
}

impl NodeTiming {
    pub fn estimated_earliest_finish(&self) -> Duration {
        self.estimated_earliest_start + self.estimated_wcet
    }

    pub fn estimated_latest_start(&self) -> Duration {
        self.estimated_latest_finish - self.estimated_wcet
    }

    pub fn slack(&self) -> Duration {
        self.estimated_latest_finish - self.estimated_earliest_finish()
    }
}

struct NodeInfo {
    task_id: u32,
    subscribe_topic_names: Vec<Cow<'static, str>>,
    publish_topic_names: Vec<Cow<'static, str>>,
    relative_deadline: Option<Duration>, // Sink node's relative deadline; None for other nodes
    timing: NodeTiming, // The WCET is declared, and `compute_timing` computes the rest.
    num_finished: u64,  // Number of DAG jobs that this node finished.
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
                    release_times: Mutex::new(BTreeMap::new()),

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

/// Computes the relative deadline of every node, as an offset from the job release, from the
/// estimated WCETs and the sink relative deadline `D`. The earliest starts are computed only to
/// check feasibility and to mark the nodes on a critical path.
///
/// - `ES(source) = 0`, and `ES(v) = max over predecessors p of (ES(p) + C(p))`.
/// - `deadline(sink) = D`, and `deadline(v) = min over successors s of (deadline(s) - C(s))`.
///
/// Fails if some node cannot finish by its latest finish, that is, if the critical path
/// exceeds `D`. It requires an acyclic DAG, which `validate_dag` ensures.
fn compute_timing(dag: &Dag) -> Result<(), DagError> {
    let dag_id = dag.id;
    let mut node = MCSNode::new();
    let mut graph = dag.graph.lock(&mut node);

    let sink_deadline = graph
        .get_sink_relative_deadline()
        .ok_or(DagError::MissingSinkDeadline(dag_id))?;

    let order = graph.topological_order();

    // Forward pass to compute per-node earliest start times.
    let mut earliest_start: BTreeMap<NodeIndex, Duration> = BTreeMap::new();
    for &idx in &order {
        let mut start = Duration::ZERO;
        for pred in graph.neighbors_directed(idx, Direction::Incoming) {
            let pred_start = earliest_start.get(&pred).copied().unwrap_or(Duration::ZERO);
            let pred_finish = pred_start
                .checked_add(graph.get_node_wcet(pred).unwrap_or(Duration::ZERO))
                .ok_or(DagError::WcetOverflow(dag_id))?;
            start = start.max(pred_finish);
        }
        earliest_start.insert(idx, start);
    }

    // Backward pass to compute per-node latest finish times.
    let mut latest_finish: BTreeMap<NodeIndex, Duration> = BTreeMap::new();
    for &idx in order.iter().rev() {
        let mut finish = sink_deadline;
        let mut has_successor = false;
        for succ in graph.neighbors_directed(idx, Direction::Outgoing) {
            let succ_finish = latest_finish.get(&succ).copied().unwrap_or(sink_deadline);
            let succ_start = succ_finish
                .checked_sub(graph.get_node_wcet(succ).unwrap_or(Duration::ZERO))
                .ok_or(DagError::InfeasibleWcet(dag_id, succ.index()))?;
            finish = if has_successor {
                finish.min(succ_start)
            } else {
                succ_start
            };
            has_successor = true;
        }
        latest_finish.insert(idx, finish);
    }

    // Check feasibility, and find the slack of every node.
    let mut slacks: BTreeMap<NodeIndex, Duration> = BTreeMap::new();
    for &idx in &order {
        let wcet = graph.get_node_wcet(idx).unwrap_or(Duration::ZERO);
        let earliest_start = earliest_start.get(&idx).copied().unwrap_or(Duration::ZERO);
        let latest_finish = latest_finish.get(&idx).copied().unwrap_or(sink_deadline);

        let earliest_finish = earliest_start
            .checked_add(wcet)
            .ok_or(DagError::WcetOverflow(dag_id))?;
        let slack = latest_finish
            .checked_sub(earliest_finish)
            .ok_or(DagError::InfeasibleWcet(dag_id, idx.index()))?;
        slacks.insert(idx, slack);
    }

    // A node is critical if it has the least slack, which only the nodes on a longest path have.
    let min_slack = slacks.values().min().copied().unwrap_or(Duration::ZERO);

    for &idx in &order {
        let info = graph
            .node_weight_mut(idx)
            .ok_or(DagError::NodeNotFound(dag_id, idx.index()))?;
        info.timing.estimated_earliest_start =
            earliest_start.get(&idx).copied().unwrap_or(Duration::ZERO);
        info.timing.estimated_latest_finish =
            latest_finish.get(&idx).copied().unwrap_or(sink_deadline);
        info.timing.is_critical = slacks.get(&idx) == Some(&min_slack);
    }

    Ok(())
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

    #[test]
    fn late_node_keeps_the_deadline_of_its_job() {
        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &["deadline_test_topic".into()]);
        let sink = dag.add_node_with_topic_edges(&["deadline_test_topic".into()], &[]);

        // A non-source node does not release a job.
        assert_eq!(dag.get_or_release_job(sink, true, || 5, |_| ()).0, 5);

        // The source node releases job 0. A later wake in job 0 keeps the deadline.
        assert_eq!(dag.get_or_release_job(source, true, || 10, |_| ()).0, 10);
        assert_eq!(dag.get_or_release_job(source, true, || 11, |_| ()).0, 10);

        // The input of job 0 can reach the sink node without a wake.
        assert!(dag.has_stale_deadline(sink));

        dag.finish_job(source);

        // A preempted source node resumes before the next period and does not release job 1.
        assert_eq!(dag.get_or_release_job(source, false, || 15, |_| ()).0, 15);
        assert_eq!(dag.get_or_release_job(source, true, || 20, |_| ()).0, 20);

        // The sink node wakes for job 0 after the release of job 1.
        assert_eq!(dag.get_or_release_job(sink, true, || 21, |_| ()).0, 10);
        assert!(!dag.has_stale_deadline(sink));

        // The source node released job 1.
        dag.finish_job(sink);
        assert!(dag.has_stale_deadline(sink));
        assert_eq!(dag.get_or_release_job(sink, true, || 22, |_| ()).0, 20);
        assert!(!dag.has_stale_deadline(sink));
        assert!(!dag.release_times.lock(&mut MCSNode::new()).contains_key(&0));
    }

    #[test]
    fn deadline_stays_until_every_node_finishes_its_job() {
        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &["retention_test_a".into()]);
        let middle = dag
            .add_node_with_topic_edges(&["retention_test_a".into()], &["retention_test_b".into()]);
        let sink = dag.add_node_with_topic_edges(&["retention_test_b".into()], &[]);

        // The source node releases jobs 0, 1, and 2.
        assert_eq!(dag.get_or_release_job(source, true, || 10, |_| ()).0, 10);
        dag.finish_job(source);
        assert_eq!(dag.get_or_release_job(source, true, || 20, |_| ()).0, 20);
        dag.finish_job(source);
        assert_eq!(dag.get_or_release_job(source, true, || 30, |_| ()).0, 30);

        // The sink node finishes job 0 before the middle node records its finish.
        dag.finish_job(sink);
        assert_eq!(dag.get_or_release_job(middle, true, || 31, |_| ()).0, 10);

        dag.finish_job(middle);
        assert_eq!(dag.get_or_release_job(middle, true, || 32, |_| ()).0, 20);
        assert_eq!(dag.get_or_release_job(sink, true, || 33, |_| ()).0, 20);

        let mut node = MCSNode::new();
        let jobs: Vec<u64> = dag.release_times.lock(&mut node).keys().copied().collect();
        assert_eq!(jobs, [1, 2]);
    }

    #[test]
    fn deadlines_of_a_stopped_node_are_capped() {
        let dag = create_dag();
        let source = dag.add_node_with_topic_edges(&[], &["cap_test_topic".into()]);
        let _sink = dag.add_node_with_topic_edges(&["cap_test_topic".into()], &[]);

        // The sink node stopped, for example by a panic, and the source node keeps releasing.
        for deadline in 0..100 {
            dag.get_or_release_job(source, true, || deadline, |_| ()).0;
            dag.finish_job(source);
        }

        let mut node = MCSNode::new();
        let release_times = dag.release_times.lock(&mut node);
        // The cap for two nodes.
        assert_eq!(
            release_times.len(),
            2 * (Attribute::default().queue_size + 1) + 1
        );
        assert_eq!(release_times.last_key_value(), Some((&99, &99)));
    }

    fn latest_finish_of(dag: &Dag, idx: NodeIndex) -> Duration {
        let mut node = MCSNode::new();
        let graph = dag.graph.lock(&mut node);
        graph
            .node_weight(idx)
            .unwrap()
            .timing
            .estimated_latest_finish
    }

    // source -> a -> sink, and source -> b -> sink.
    fn diamond(prefix: &str) -> (Arc<Dag>, [NodeIndex; 4]) {
        let dag = create_dag();
        let t = |s: &str| -> Cow<'static, str> { alloc::format!("{prefix}_{s}").into() };
        let source = dag.add_node_with_topic_edges(&[], &[t("sa"), t("sb")]);
        let a = dag.add_node_with_topic_edges(&[t("sa")], &[t("as")]);
        let b = dag.add_node_with_topic_edges(&[t("sb")], &[t("bs")]);
        let sink = dag.add_node_with_topic_edges(&[t("as"), t("bs")], &[]);
        dag.set_relative_deadline(sink, Duration::from_millis(100))
            .unwrap();
        (dag, [source, a, b, sink])
    }

    #[test]
    fn zero_wcets_give_the_sink_deadline_to_every_node() {
        let (dag, nodes) = diamond("timing_zero");
        assert!(compute_timing(&dag).is_ok());
        for idx in nodes {
            assert_eq!(latest_finish_of(&dag, idx), Duration::from_millis(100));
        }
    }

    #[test]
    fn latest_finish_follows_the_downstream_wcets() {
        let (dag, [source, a, b, sink]) = diamond("timing_diamond");
        dag.set_node_wcet(source, Duration::from_millis(10))
            .unwrap();
        dag.set_node_wcet(a, Duration::from_millis(30)).unwrap();
        dag.set_node_wcet(b, Duration::from_millis(5)).unwrap();
        dag.set_node_wcet(sink, Duration::from_millis(20)).unwrap();
        assert!(compute_timing(&dag).is_ok());

        assert_eq!(latest_finish_of(&dag, sink), Duration::from_millis(100));
        assert_eq!(latest_finish_of(&dag, a), Duration::from_millis(80));
        assert_eq!(latest_finish_of(&dag, b), Duration::from_millis(80));
        // The slower branch `a` bounds the source.
        assert_eq!(latest_finish_of(&dag, source), Duration::from_millis(50));
    }

    #[test]
    fn critical_path_over_the_deadline_is_rejected() {
        let (dag, [source, a, _b, sink]) = diamond("timing_infeasible");
        dag.set_node_wcet(source, Duration::from_millis(50))
            .unwrap();
        dag.set_node_wcet(a, Duration::from_millis(40)).unwrap();
        dag.set_node_wcet(sink, Duration::from_millis(20)).unwrap();
        assert!(matches!(
            compute_timing(&dag),
            Err(DagError::InfeasibleWcet(..))
        ));
    }

    #[test]
    fn nodes_on_the_longest_path_are_critical() {
        let (dag, [source, a, b, sink]) = diamond("timing_critical");
        dag.set_node_wcet(source, Duration::from_millis(10))
            .unwrap();
        dag.set_node_wcet(a, Duration::from_millis(30)).unwrap();
        dag.set_node_wcet(b, Duration::from_millis(5)).unwrap();
        dag.set_node_wcet(sink, Duration::from_millis(20)).unwrap();
        assert!(compute_timing(&dag).is_ok());

        // The path source -> a -> sink is 60 ms, shorter than D, and still the longest.
        let critical = |idx| {
            dag.get_or_release_job(idx, false, || 0, |timing| timing.is_critical)
                .1
        };
        assert!(critical(source));
        assert!(critical(a));
        assert!(!critical(b));
        assert!(critical(sink));
    }

    #[test]
    fn released_job_returns_release_time_and_node_timing() {
        let (dag, [source, a, _b, sink]) = diamond("timing_job");
        dag.set_node_wcet(sink, Duration::from_millis(20)).unwrap();
        dag.set_node_wcet(a, Duration::from_millis(30)).unwrap();
        dag.set_node_wcet(source, Duration::from_millis(10))
            .unwrap();
        assert!(compute_timing(&dag).is_ok());

        let (release_time, (wcet, earliest_start, latest_finish)) = dag.get_or_release_job(
            source,
            true,
            || 1_000,
            |timing| {
                (
                    timing.estimated_wcet,
                    timing.estimated_earliest_start,
                    timing.estimated_latest_finish,
                )
            },
        );
        assert_eq!(release_time, 1_000);
        assert_eq!(wcet, Duration::from_millis(10));
        assert_eq!(earliest_start, Duration::ZERO);
        assert_eq!(latest_finish, Duration::from_millis(50));

        let (release_time, (earliest_start, latest_finish)) = dag.get_or_release_job(
            sink,
            true,
            || 2_000,
            |timing| {
                (
                    timing.estimated_earliest_start,
                    timing.estimated_latest_finish,
                )
            },
        );
        assert_eq!(release_time, 1_000); // The job of the source node.
        assert_eq!(earliest_start, Duration::from_millis(40));
        assert_eq!(latest_finish, Duration::from_millis(100));
    }
}
