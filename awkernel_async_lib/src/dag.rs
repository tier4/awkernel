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
//! # Example Usage
//!
//! See the `applications/tests/test_dag` example for practical usage.
//!
//! # Notes
//!
//!  The assumption is that there is one sink vertex and one source vertexe.
//!
mod graph;
mod unionfind;
mod visit;

#[cfg(feature = "perf")]
mod performance;

use crate::{
    dag::graph::{
        algo::{connected_components, is_cyclic_directed},
        direction::Direction,
        NodeIndex,
    },
    scheduler::SchedulerType,
    sleep, Attribute, MultipleReceiver, MultipleSender, VectorToPublishers, VectorToSubscribers,
};
use alloc::{
    borrow::Cow,
    boxed::Box,
    collections::{btree_map, BTreeMap},
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::{cmp::Ordering, future::Future, pin::Pin, time::Duration};

#[cfg(feature = "perf")]
use performance::ResponseInfo;

static DAGS: Mutex<Dags> = Mutex::new(Dags::new()); // Set of DAGs.
static PENDING_TASKS: Mutex<BTreeMap<u32, Vec<PendingTask>>> = Mutex::new(BTreeMap::new()); // key: dag_id
static SOURCE_PENDING_TASKS: Mutex<BTreeMap<u32, PendingTask>> = Mutex::new(BTreeMap::new()); // key: dag_id

type MeasureF = Arc<dyn Fn() + Send + Sync + 'static>;

pub enum DagError {
    NotWeaklyConnected(u32),
    ContainsCycle(u32),
    MissingPendingTasks(u32),
    MultipleSourceNodes(u32),
    MultipleSinkNodes(u32),
    NoPublisherFound(u32, usize),  //dag_id, node_id
    NoSubscriberFound(u32, usize), //dag_id, node_id,
}

impl core::fmt::Display for DagError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DagError::NotWeaklyConnected(id) => write!(f, "DAG#{id} is not weakly connected"),
            DagError::ContainsCycle(id) => write!(f, "DAG#{id} contains a cycle"),
            DagError::MissingPendingTasks(id) => write!(f, "DAG#{id} has missing pending tasks"),
            DagError::MultipleSourceNodes(id) => write!(f, "DAG#{id} has multiple source nodes"),
            DagError::MultipleSinkNodes(id) => write!(f, "DAG#{id} has multiple sink nodes"),
            DagError::NoPublisherFound(dag_id, node_id) => {
                write!(f, "DAG #{} Node #{}: One or more subscribed topics have no corresponding publisher", dag_id, node_id)
            }
            DagError::NoSubscriberFound(dag_id, node_id) => {
                write!(f, "DAG #{} Node #{}: One or more published topics have no corresponding subscriber", dag_id, node_id)
            }
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
    subscribe_topics: Vec<Cow<'static, str>>,
    publish_topics: Vec<Cow<'static, str>>,
    relative_deadline: Option<Duration>,
}

pub struct Dag {
    id: u32,
    graph: Mutex<graph::Graph<NodeInfo, u32>>, //TODO: Change to edge attribute

    #[cfg(feature = "perf")]
    response_info: Mutex<ResponseInfo>,
}

impl Dag {
    pub fn get_id(&self) -> u32 {
        self.id
    }

    pub fn node_count(&self) -> usize {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        graph.node_count()
    }

    pub fn edge_count(&self) -> usize {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        graph.edge_count()
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

    fn set_relative_deadline(&self, node_idx: NodeIndex, deadline: Duration) {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        graph.node_weight_mut(node_idx).unwrap().relative_deadline = Some(deadline);
    }

    fn add_node_with_topic_edges(
        &self,
        subscribe_topic_names: &[Cow<'static, str>],
        publish_topic_names: &[Cow<'static, str>],
    ) -> NodeIndex {
        let add_node_info = NodeInfo {
            task_id: 0, // Temporary task_id
            subscribe_topics: subscribe_topic_names.to_vec(),
            publish_topics: publish_topic_names.to_vec(),
            relative_deadline: None,
        };

        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        let add_node_idx = graph.add_node(add_node_info);

        for node_idx in graph.node_indices() {
            if let Some(node_info) = graph.node_weight(node_idx) {
                let subscribe_match = subscribe_topic_names
                    .iter()
                    .any(|sub| node_info.publish_topics.contains(sub));

                let publish_match = publish_topic_names
                    .iter()
                    .any(|pub_| node_info.subscribe_topics.contains(pub_));

                if subscribe_match {
                    graph.add_edge(node_idx, add_node_idx, 0);
                }

                if publish_match {
                    graph.add_edge(add_node_idx, node_idx, 0);
                }
            }
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
    {
        let node_idx = self.add_node_with_topic_edges(&subscribe_topic_names, &publish_topic_names);

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
    {
        let node_idx = self.add_node_with_topic_edges(&Vec::new(), &publish_topic_names);

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
    {
        let node_idx = self.add_node_with_topic_edges(&subscribe_topic_names, &Vec::new());
        self.set_relative_deadline(node_idx, relative_deadline);

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
                    )
                    .await
                })
            }));
    }
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

/// This function detects inconsistencies between the declared topic connections and the actual graph structure.
/// It prevents mis configurations such as topics that are published but have no subscriber and topics that are subscribed to but have no publisher,
/// which can lead to unintentional message loss or reactors waiting forever.
fn validate_edge_connect(dag: &Dag) -> Result<(), DagError> {
    type DagErrorFn = fn(u32, usize) -> DagError;

    let mut node = MCSNode::new();
    let graph = dag.graph.lock(&mut node);
    for node_id in graph.node_indices() {
        let node_info = graph.node_weight(node_id).unwrap();
        for direction in [Direction::Incoming, Direction::Outgoing] {
            let (expect_num, few_error) = match direction {
                Direction::Incoming => (
                    node_info.subscribe_topics.len(),
                    DagError::NoPublisherFound as DagErrorFn,
                ),
                Direction::Outgoing => (
                    node_info.publish_topics.len(),
                    DagError::NoSubscriberFound as DagErrorFn,
                ),
            };

            let actual_num = graph.neighbors_directed(node_id, direction).count();
            if actual_num < expect_num {
                return Err(few_error(dag.id, node_id.index()));
            }
        }
    }

    Ok(())
}

fn validate_dag(dag: &Dag) -> Result<(), DagError> {
    let mut pending_node = MCSNode::new();
    if PENDING_TASKS.lock(&mut pending_node).get(&dag.id).is_none() {
        return Err(DagError::MissingPendingTasks(dag.id));
    }

    {
        let mut graph_node = MCSNode::new();
        let graph = dag.graph.lock(&mut graph_node);
        if connected_components(&*graph) != 1 {
            return Err(DagError::NotWeaklyConnected(dag.id));
        }
        if is_cyclic_directed(&*graph) {
            return Err(DagError::ContainsCycle(dag.id));
        }
    }

    if dag.get_source_nodes().len() > 1 {
        return Err(DagError::MultipleSourceNodes(dag.id));
    }
    if dag.get_sink_nodes().len() > 1 {
        return Err(DagError::MultipleSinkNodes(dag.id));
    }

    validate_edge_connect(dag)?;
    Ok(())
}

pub async fn finish_create_dags(dags: &[Arc<Dag>]) -> Result<(), DagError> {
    for dag in dags {
        let dag_id = dag.id;
        assert!(
            get_dag(dag_id).is_some(),
            "Invariant Violation: DAG with id {dag_id} must exist, but was not found.",
        );

        validate_dag(dag)?;

        let pending_tasks = {
            let mut node = MCSNode::new();
            let mut lock = PENDING_TASKS.lock(&mut node);
            lock.remove(&dag_id).unwrap()
        };

        for task in pending_tasks {
            let task_id = (task.spawn)().await;
            let mut graph_node = MCSNode::new();
            let mut graph = dag.graph.lock(&mut graph_node);
            if let Some(node_info) = graph.node_weight_mut(task.node_idx) {
                node_info.task_id = task_id;
            }
        }

        // To prevent message drops, source reactor is spawned after all subsequent reactors have been spawned.
        // If the source reactor is not spawned last, it may publish a message before subsequent reactors are ready to receive it.
        let source_pending_task = {
            let mut node = MCSNode::new();
            let mut lock = SOURCE_PENDING_TASKS.lock(&mut node);
            lock.remove(&dag_id).unwrap()
        };

        let task_id = (source_pending_task.spawn)().await;
        let mut graph_node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut graph_node);
        if let Some(node_info) = graph.node_weight_mut(source_pending_task.node_idx) {
            node_info.task_id = task_id;
        }
    }

    Ok(())
}

async fn spawn_reactor<F, Args, Ret>(
    reactor_name: Cow<'static, str>,
    f: F,
    subscribe_topic_names: Vec<Cow<'static, str>>,
    publish_topic_names: Vec<Cow<'static, str>>,
    sched_type: SchedulerType,
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
    let future = async move {
        let publishers = <Ret as VectorToPublishers>::create_publishers(
            publish_topic_names,
            Attribute::default(),
        );

        let subscribers: <Args as VectorToSubscribers>::Subscribers =
            Args::create_subscribers(subscribe_topic_names, Attribute::default());

        loop {
            let args: <<Args as VectorToSubscribers>::Subscribers as MultipleReceiver>::Item =
                subscribers.recv_all().await;
            let results = f(args);
            publishers.send_all(results).await;
        }
    };

    crate::task::spawn(reactor_name, future, sched_type)
}

async fn spawn_periodic_reactor<F, Ret>(
    reactor_name: Cow<'static, str>,
    f: F,
    publish_topic_names: Vec<Cow<'static, str>>,
    sched_type: SchedulerType,
    period: Duration,
    _release_measure: Option<MeasureF>,
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

    // TODO(sykwer): Improve mechanisms to more closely align performance behavior with the DAG scheduling model.
    let future = async move {
        let publishers = <Ret as VectorToPublishers>::create_publishers(
            publish_topic_names,
            Attribute::default(),
        );

        loop {
            let results = f();
            publishers.send_all(results).await;
            sleep(period).await; //TODO(sykwer):Improve the accuracy of the period.
            #[cfg(feature = "perf")]
            periodic_measure();
        }
    };

    let task_id = crate::task::spawn(reactor_name, future, sched_type);

    #[cfg(feature = "perf")]
    release_measure();

    task_id
}

async fn spawn_sink_reactor<F, Args>(
    reactor_name: Cow<'static, str>,
    f: F,
    subscribe_topic_names: Vec<Cow<'static, str>>,
    sched_type: SchedulerType,
) -> u32
where
    F: Fn(<Args::Subscribers as MultipleReceiver>::Item) + Send + 'static,
    Args: VectorToSubscribers,
    Args::Subscribers: Send,
{
    let future = async move {
        let subscribers: <Args as VectorToSubscribers>::Subscribers =
            Args::create_subscribers(subscribe_topic_names, Attribute::default());

        loop {
            let args: <<Args as VectorToSubscribers>::Subscribers as MultipleReceiver>::Item =
                subscribers.recv_all().await;
            f(args);
        }
    };

    crate::task::spawn(reactor_name, future, sched_type)
}
