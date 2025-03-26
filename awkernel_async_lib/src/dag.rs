mod graph;
mod unionfind;
mod visit;

use crate::{
    dag::graph::{
        algo::{connected_components, is_cyclic_directed},
        NodeIndex,
    },
    scheduler::SchedulerType,
    spawn_periodic_reactor, spawn_reactor, MultipleReceiver, MultipleSender, VectorToPublishers,
    VectorToSubscribers,
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

pub enum DagError {
    NotWeaklyConnected(u32),
    ContainsCycle(u32),
}

#[derive(Debug, Clone)]
pub struct NodeInfo {
    task_id: u32,
    subscribe_topics: Vec<Cow<'static, str>>,
    publish_topics: Vec<Cow<'static, str>>,
}

pub struct Dag {
    pub id: u32,
    pub graph: Mutex<graph::Graph<NodeInfo, u32>>, //TODO: Change to edge attribute
    pending_tasks: Mutex<Vec<PendingTask>>,
}

struct PendingTask {
    node_idx: NodeIndex,
    func: Box<dyn FnOnce() -> Pin<Box<dyn Future<Output = u32> + Send>> + Send>,
}

impl Dag {
    fn add_node_with_topic_edges(
        &self,
        subscribe_topic_names: &[Cow<'static, str>],
        publish_topic_names: &[Cow<'static, str>],
    ) -> NodeIndex {
        let add_node_info = NodeInfo {
            task_id: 0, // Temporary task_id
            subscribe_topics: subscribe_topic_names.to_vec(),
            publish_topics: publish_topic_names.to_vec(),
        };

        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        let add_node_idx = graph.add_node(add_node_info);

        for node_idx in graph.node_indices() {
            if node_idx != add_node_idx {
                if let Some(node_info) = graph.node_weight(node_idx).cloned() {
                    for subscribe_topic in subscribe_topic_names {
                        if node_info.publish_topics.contains(subscribe_topic) {
                            graph.add_edge(node_idx, add_node_idx, 0);
                        }
                    }
                    for publish_topic in publish_topic_names {
                        if node_info.subscribe_topics.contains(publish_topic) {
                            graph.add_edge(add_node_idx, node_idx, 0);
                        }
                    }
                }
            }
        }
        add_node_idx
    }

    pub async fn spawn_reactor<F, Args, Ret>(
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
        let mut pending_tasks = self.pending_tasks.lock(&mut node);

        pending_tasks.push(PendingTask {
            node_idx,
            func: Box::new(move || {
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
            }),
        });
    }

    pub async fn spawn_periodic_reactor<F, Ret>(
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
        let mut pending_tasks = self.pending_tasks.lock(&mut node);

        pending_tasks.push(PendingTask {
            node_idx,
            func: Box::new(move || {
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
            }),
        });
    }
}

/// DAGs.
#[derive(Default)]
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
            if id == 0 {
                id += 1;
            }

            // Find an unused DAG ID.
            if let btree_map::Entry::Vacant(e) = self.id_to_dag.entry(id) {
                let dag = Arc::new(Dag {
                    id,
                    graph: Mutex::new(graph::Graph::new()),
                    pending_tasks: Mutex::new(Vec::new()),
                });

                e.insert(dag.clone());
                self.candidate_id = id;

                return dag;
            } else {
                // The candidate DAG ID is already used.
                // Check next candidate.
                id += 1;
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

pub async fn finish_create_dags(dags: &[Arc<Dag>]) -> Result<(), DagError> {
    for dag in dags {
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

        let mut node = MCSNode::new();
        let pending_tasks: Vec<_> = dag.pending_tasks.lock(&mut node).drain(..).collect();

        for task in pending_tasks {
            let task_id = (task.func)().await;
            let mut graph_node = MCSNode::new();
            let mut graph = dag.graph.lock(&mut graph_node);
            if let Some(node_info) = graph.node_weight_mut(task.node_idx) {
                node_info.task_id = task_id;
            }
        }
    }

    Ok(())
}
