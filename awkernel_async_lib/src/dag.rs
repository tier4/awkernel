mod graph;
mod unionfind;
mod visit;

use crate::{
    dag::graph::{
        algo::{connected_components, is_cyclic_directed},
        NodeIndex,
    },
    scheduler::SchedulerType,
    spawn_periodic_reactor, spawn_reactor, spawn_sink_reactor, MultipleReceiver, MultipleSender,
    VectorToPublishers, VectorToSubscribers,
};
use alloc::{
    borrow::Cow,
    boxed::Box,
    collections::{btree_map, BTreeMap},
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::{future::Future, pin::Pin, time::Duration};

static DAGS: Mutex<Dags> = Mutex::new(Dags::new()); // Set of DAGs.
static PENDING_TASKS: Mutex<BTreeMap<u32, Vec<PendingTask>>> = Mutex::new(BTreeMap::new()); // key: dag_id

pub enum DagError {
    NotWeaklyConnected(u32),
    ContainsCycle(u32),
    MissingPendingTasks(u32),
}

impl core::fmt::Display for DagError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DagError::NotWeaklyConnected(id) => write!(f, "DAG#{} is not weakly connected", id),
            DagError::ContainsCycle(id) => write!(f, "DAG#{} contains a cycle", id),
            DagError::MissingPendingTasks(id) => write!(f, "DAG#{} has missing pending tasks", id),
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
                        reactor_name.clone(),
                        f,
                        subscribe_topic_names.clone(),
                        publish_topic_names.clone(),
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

        let mut node = MCSNode::new();
        let mut pending_tasks = PENDING_TASKS.lock(&mut node);

        pending_tasks
            .entry(self.id)
            .or_default()
            .push(PendingTask::new(node_idx, move || {
                Box::pin(async move {
                    spawn_periodic_reactor::<F, Ret>(
                        reactor_name.clone(),
                        f,
                        publish_topic_names.clone(),
                        sched_type,
                        period,
                    )
                    .await
                })
            }));
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

        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);

        graph.node_weight_mut(node_idx).unwrap().relative_deadline = Some(relative_deadline);

        let mut node = MCSNode::new();
        let mut pending_tasks = PENDING_TASKS.lock(&mut node);

        pending_tasks
            .entry(self.id)
            .or_default()
            .push(PendingTask::new(node_idx, move || {
                Box::pin(async move {
                    spawn_sink_reactor::<F, Args>(
                        reactor_name.clone(),
                        f,
                        subscribe_topic_names.clone(),
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

fn validate_dag(dag: &Dag) -> Result<(), DagError> {
    let mut pending_node = MCSNode::new();
    if PENDING_TASKS.lock(&mut pending_node).get(&dag.id).is_none() {
        return Err(DagError::MissingPendingTasks(dag.id));
    }

    let mut graph_node = MCSNode::new();
    let graph = dag.graph.lock(&mut graph_node);
    if connected_components(&*graph) != 1 {
        return Err(DagError::NotWeaklyConnected(dag.id));
    }
    if is_cyclic_directed(&*graph) {
        return Err(DagError::ContainsCycle(dag.id));
    }
    Ok(())
}

pub async fn finish_create_dags(dags: &[Arc<Dag>]) -> Result<(), DagError> {
    for dag in dags {
        validate_dag(dag)?;

        let pending_tasks = {
            let mut node = MCSNode::new();
            let mut lock = PENDING_TASKS.lock(&mut node);
            lock.remove(&dag.id).unwrap()
        };

        for task in pending_tasks {
            let task_id = (task.spawn)().await;
            let mut graph_node = MCSNode::new();
            let mut graph = dag.graph.lock(&mut graph_node);
            if let Some(node_info) = graph.node_weight_mut(task.node_idx) {
                node_info.task_id = task_id;
            }
        }
    }

    Ok(())
}
