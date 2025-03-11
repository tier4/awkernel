pub mod graph;

use alloc::{
    borrow::Cow,
    boxed::Box,
    collections::{btree_map, BTreeMap, BTreeSet},
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::{future::Future, pin::Pin, time::Duration};

use crate::dag::graph::{direction::Direction, NodeIndex};
use crate::{
    scheduler::SchedulerType, spawn_periodic_reactor, spawn_reactor, MultipleReceiver,
    MultipleSender, VectorToPublishers, VectorToSubscribers,
};

static DAGS: Mutex<Dags> = Mutex::new(Dags::new()); // Set of DAGs.

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
    pub fn get_id(&self) -> u32 {
        self.id
    }

    fn add_node(&self, graph: &mut graph::Graph<NodeInfo, u32>, data: NodeInfo) -> NodeIndex {
        graph.add_node(data)
    }

    fn add_edge(
        &self,
        graph: &mut graph::Graph<NodeInfo, u32>,
        source: NodeIndex,
        target: NodeIndex,
    ) -> graph::EdgeIndex {
        graph.add_edge(source, target, 0) // 0 is the temporary weight
    }

    fn node_count(&self, graph: &graph::Graph<NodeInfo, u32>) -> usize {
        graph.node_count()
    }

    fn node_indices(&self, graph: &graph::Graph<NodeInfo, u32>) -> Vec<NodeIndex> {
        graph.node_indices().collect()
    }

    fn node_weight(
        &self,
        graph: &graph::Graph<NodeInfo, u32>,
        node_idx: NodeIndex,
    ) -> Option<NodeInfo> {
        graph.node_weight(node_idx).cloned()
    }

    fn neighbors_directed(
        &self,
        graph: &graph::Graph<NodeInfo, u32>,
        node_idx: NodeIndex,
        dir: Direction,
    ) -> Vec<NodeIndex> {
        graph.neighbors_directed(node_idx, dir).collect()
    }

    fn neighbors_undirected(
        &self,
        graph: &graph::Graph<NodeInfo, u32>,
        node_idx: NodeIndex,
    ) -> Vec<NodeIndex> {
        graph.neighbors_undirected(node_idx).collect()
    }

    fn build_reactor_graph(
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
        let add_node_idx = self.add_node(&mut graph, add_node_info);

        for node_idx in self.node_indices(&graph) {
            if node_idx != add_node_idx {
                if let Some(node_info) = self.node_weight(&graph, node_idx) {
                    for subscribe_topic in subscribe_topic_names {
                        if node_info.publish_topics.contains(subscribe_topic) {
                            self.add_edge(&mut graph, node_idx, add_node_idx);
                        }
                    }
                    for publish_topic in publish_topic_names {
                        if node_info.subscribe_topics.contains(publish_topic) {
                            self.add_edge(&mut graph, add_node_idx, node_idx);
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
        let node_idx = self.build_reactor_graph(&subscribe_topic_names, &publish_topic_names);

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
        let node_idx = self.build_reactor_graph(&Vec::new(), &publish_topic_names);

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

    fn is_weakly_connected(&self, graph: &graph::Graph<NodeInfo, u32>) -> bool {
        if self.node_count(graph) == 0 {
            return false;
        }

        let mut visited: BTreeSet<NodeIndex> = BTreeSet::new();
        let mut stack: Vec<NodeIndex> = Vec::new();

        if let Some(start_node) = self.node_indices(graph).first() {
            stack.push(*start_node);
            visited.insert(*start_node);
        }

        while let Some(node_idx) = stack.pop() {
            for neighbor in self.neighbors_undirected(graph, node_idx) {
                if !visited.contains(&neighbor) {
                    visited.insert(neighbor);
                    stack.push(neighbor);
                }
            }
        }

        visited.len() == self.node_count(&graph)
    }

    fn is_cycle(&self, graph: &graph::Graph<NodeInfo, u32>) -> bool {
        let mut visited: BTreeSet<NodeIndex> = BTreeSet::new();
        let mut stack: Vec<NodeIndex> = Vec::new();

        for node_idx in self.node_indices(graph) {
            if !visited.contains(&node_idx) && self.dfs(graph, node_idx, &mut visited, &mut stack) {
                return true;
            }
        }

        false
    }

    fn dfs(
        &self,
        graph: &graph::Graph<NodeInfo, u32>,
        node_idx: NodeIndex,
        visited: &mut BTreeSet<NodeIndex>,
        stack: &mut Vec<NodeIndex>,
    ) -> bool {
        if stack.contains(&node_idx) {
            return true;
        }
        if visited.contains(&node_idx) {
            return false;
        }

        visited.insert(node_idx);
        stack.push(node_idx);

        for neighbor in self.neighbors_directed(graph, node_idx, Direction::Outgoing) {
            if self.dfs(graph, neighbor, visited, stack) {
                return true;
            }
        }

        stack.pop();
        false
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

pub async fn finish_create_dag(dags: &[Arc<Dag>]) {
    for dag in dags {
        {
            let mut graph_node = MCSNode::new();
            let graph = dag.graph.lock(&mut graph_node);
            if !dag.is_weakly_connected(&graph) {
                panic!("DAG ID {} is not weakly connected", dag.get_id());
            }
            if dag.is_cycle(&graph) {
                panic!("DAG ID {} is cycle", dag.get_id());
            }
        }

        let mut node = MCSNode::new();
        let pending_tasks: Vec<_> = dag.pending_tasks.lock(&mut node).drain(..).collect();

        for task in pending_tasks {
            let task_id = (task.func)().await;

            let mut graph_node = MCSNode::new();
            let mut graph = dag.graph.lock(&mut graph_node);
            // Use graph's API to meet lifetime requirements
            if let Some(node_info) = graph.node_weight_mut(task.node_idx) {
                node_info.task_id = task_id;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn create_node_info(node_id: u32) -> NodeInfo {
        NodeInfo {
            task_id: node_id,
            subscribe_topics: Vec::new(),
            publish_topics: Vec::new(),
        }
    }

    #[test]
    fn test_add_node() {
        let dag = create_dag();
        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);

        dag.add_node(&mut graph, create_node_info(1));
        dag.add_node(&mut graph, create_node_info(2));
        dag.add_node(&mut graph, create_node_info(3));

        assert_eq!(dag.node_count(&graph), 3);
    }

    #[test]
    fn test_add_edge() {
        let dag = create_dag();
        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);

        let a = dag.add_node(&mut graph, create_node_info(1));
        let b = dag.add_node(&mut graph, create_node_info(2));
        let c = dag.add_node(&mut graph, create_node_info(3));

        dag.add_edge(&mut graph, a, b);
        dag.add_edge(&mut graph, a, c);
        dag.add_edge(&mut graph, b, c);

        let edge_count = graph.edge_count();

        assert_eq!(edge_count, 3);
    }

    #[test]
    fn test_neighbors_directed() {
        let dag = create_dag();
        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);

        let a = dag.add_node(&mut graph, create_node_info(1));
        let b = dag.add_node(&mut graph, create_node_info(2));
        let c = dag.add_node(&mut graph, create_node_info(3));

        dag.add_edge(&mut graph, a, b);
        dag.add_edge(&mut graph, a, c);
        dag.add_edge(&mut graph, b, c);

        let neighbors = dag.neighbors_directed(&graph, b, Direction::Outgoing);
        assert_eq!(neighbors.len(), 1);
        assert_eq!(neighbors.contains(&c), true);
        assert_eq!(neighbors.contains(&a), false);
    }

    #[test]
    fn test_neighbors_undirected() {
        let dag = create_dag();
        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);

        let a = dag.add_node(&mut graph, create_node_info(1));
        let b = dag.add_node(&mut graph, create_node_info(2));
        let c = dag.add_node(&mut graph, create_node_info(3));
        let d = dag.add_node(&mut graph, create_node_info(4));

        dag.add_edge(&mut graph, a, b);
        dag.add_edge(&mut graph, a, c);
        dag.add_edge(&mut graph, b, d);

        let neighbors = dag.neighbors_undirected(&graph, b);
        assert_eq!(neighbors.len(), 2);
        assert_eq!(neighbors.contains(&d), true);
        assert_eq!(neighbors.contains(&a), true);
    }

    #[test]
    fn test_is_weakly_connected_true() {
        let dag = create_dag();

        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);

        let a = dag.add_node(&mut graph, create_node_info(1));
        let b = dag.add_node(&mut graph, create_node_info(2));
        let c = dag.add_node(&mut graph, create_node_info(3));

        dag.add_edge(&mut graph, a, b);
        dag.add_edge(&mut graph, b, c);

        assert_eq!(dag.is_weakly_connected(&graph), true);
    }

    #[test]
    fn test_is_weakly_connected_false() {
        let dag = create_dag();

        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);

        let a = dag.add_node(&mut graph, create_node_info(1));
        let b = dag.add_node(&mut graph, create_node_info(2));
        dag.add_node(&mut graph, create_node_info(3));

        dag.add_edge(&mut graph, a, b);

        assert_eq!(dag.is_weakly_connected(&graph), false);
    }

    #[test]
    fn test_is_cycle_true() {
        let dag = create_dag();

        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);

        let a = dag.add_node(&mut graph, create_node_info(1));
        let b = dag.add_node(&mut graph, create_node_info(2));
        let c = dag.add_node(&mut graph, create_node_info(3));

        dag.add_edge(&mut graph, a, b);
        dag.add_edge(&mut graph, b, c);
        dag.add_edge(&mut graph, c, a);

        assert_eq!(dag.is_cycle(&graph), true);
    }

    #[test]
    fn test_is_cycle_false() {
        let dag = create_dag();

        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);

        let a = dag.add_node(&mut graph, create_node_info(1));
        let b = dag.add_node(&mut graph, create_node_info(2));
        let c = dag.add_node(&mut graph, create_node_info(3));

        dag.add_edge(&mut graph, a, b);
        dag.add_edge(&mut graph, b, c);

        assert_eq!(dag.is_cycle(&graph), false);
    }
}
