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
    pub fn add_node(&self, data: NodeInfo) -> NodeIndex {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        self.add_node_with_lock(&mut graph, data)
    }

    pub fn add_edge(&self, source: NodeIndex, target: NodeIndex) -> graph::EdgeIndex {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        self.add_edge_with_lock(&mut graph, source, target)
    }

    pub fn remove_node(&self, node_idx: NodeIndex) {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        graph.remove_node(node_idx);
    }

    pub fn remove_edge(&self, edge_idx: graph::EdgeIndex) {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        graph.remove_edge(edge_idx);
    }

    fn add_node_with_lock(
        &self,
        graph: &mut graph::Graph<NodeInfo, u32>,
        data: NodeInfo,
    ) -> NodeIndex {
        graph.add_node(data)
    }

    fn add_edge_with_lock(
        &self,
        graph: &mut graph::Graph<NodeInfo, u32>,
        source: NodeIndex,
        target: NodeIndex,
    ) -> graph::EdgeIndex {
        graph.add_edge(source, target, 0) // 0 is the temporary weight
    }

    pub fn node_count(&self) -> usize {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        self.node_count_with_lock(&graph)
    }

    pub fn edge_count(&self) -> usize {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        graph.edge_count()
    }

    fn node_count_with_lock(&self, graph: &graph::Graph<NodeInfo, u32>) -> usize {
        graph.node_count()
    }

    fn node_indices_with_lock(&self, graph: &graph::Graph<NodeInfo, u32>) -> Vec<NodeIndex> {
        graph.node_indices().collect()
    }

    fn node_weight_with_lock(
        &self,
        graph: &graph::Graph<NodeInfo, u32>,
        node_idx: NodeIndex,
    ) -> Option<NodeInfo> {
        graph.node_weight(node_idx).cloned()
    }

    fn neighbors_directed_with_lock(
        &self,
        graph: &graph::Graph<NodeInfo, u32>,
        node_idx: NodeIndex,
        dir: Direction,
    ) -> Vec<NodeIndex> {
        graph.neighbors_directed(node_idx, dir).collect()
    }

    fn neighbors_undirected_with_lock(
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
        let add_node_idx = self.add_node_with_lock(&mut graph, add_node_info);

        for node_idx in self.node_indices_with_lock(&mut graph) {
            if node_idx != add_node_idx {
                if let Some(node_info) = self.node_weight_with_lock(&mut graph, node_idx) {
                    for subscribe_topic in subscribe_topic_names {
                        if node_info.publish_topics.contains(subscribe_topic) {
                            self.add_edge_with_lock(&mut graph, node_idx, add_node_idx);
                        }
                    }
                    for publish_topic in publish_topic_names {
                        if node_info.subscribe_topics.contains(publish_topic) {
                            self.add_edge_with_lock(&mut graph, add_node_idx, node_idx);
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
            node_idx: node_idx,
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

    fn get_boundary_nodes(&self, direction: Direction) -> Option<Vec<NodeIndex>> {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);

        let boundary_nodes: Vec<NodeIndex> = self
            .node_indices_with_lock(&graph)
            .into_iter()
            .filter(|&node_idx| {
                self.neighbors_directed_with_lock(&graph, node_idx, direction)
                    .is_empty()
            })
            .collect();

        (!boundary_nodes.is_empty()).then_some(boundary_nodes)
    }

    fn get_source_nodes(&self) -> Option<Vec<NodeIndex>> {
        self.get_boundary_nodes(Direction::Incoming)
    }

    fn get_sink_nodes(&self) -> Option<Vec<NodeIndex>> {
        self.get_boundary_nodes(Direction::Outgoing)
    }

    fn is_weakly_connected(&self) -> bool {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);

        if self.node_count_with_lock(&graph) == 0 {
            return false;
        }

        let mut visited: BTreeSet<NodeIndex> = BTreeSet::new();
        let mut stack: Vec<NodeIndex> = Vec::new();

        if let Some(start_node) = self.node_indices_with_lock(&graph).first() {
            stack.push(*start_node);
            visited.insert(*start_node);
        }

        while let Some(node_idx) = stack.pop() {
            for neighbor in self.neighbors_undirected_with_lock(&graph, node_idx) {
                if !visited.contains(&neighbor) {
                    visited.insert(neighbor);
                    stack.push(neighbor);
                }
            }
        }

        visited.len() == self.node_count_with_lock(&graph)
    }

    fn is_cycle(&self) -> bool {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);

        let mut visited: BTreeSet<NodeIndex> = BTreeSet::new();
        let mut stack: Vec<NodeIndex> = Vec::new();

        for node_idx in self.node_indices_with_lock(&graph) {
            if !visited.contains(&node_idx) && self.dfs(&graph, node_idx, &mut visited, &mut stack)
            {
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

        for neighbor in self.neighbors_directed_with_lock(&graph, node_idx, Direction::Outgoing) {
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

    fn create(&mut self) -> u32 {
        let mut id = self.candidate_id;
        loop {
            if id == 0 {
                id += 1;
            }

            // Find an unused DAG ID.
            if let btree_map::Entry::Vacant(e) = self.id_to_dag.entry(id) {
                let dag = Dag {
                    id,
                    graph: Mutex::new(graph::Graph::new()),
                    pending_tasks: Mutex::new(Vec::new()),
                };

                e.insert(Arc::new(dag));
                self.candidate_id = id;

                return id;
            } else {
                // The candidate DAG ID is already used.
                // Check next candidate.
                id += 1;
            }
        }
    }
}

pub fn create_dag() -> u32 {
    let mut node = MCSNode::new();
    let mut dags = DAGS.lock(&mut node);
    dags.create()
}

pub fn get_dag(id: u32) -> Option<Arc<Dag>> {
    let mut node = MCSNode::new();
    let dags = DAGS.lock(&mut node);
    dags.id_to_dag.get(&id).cloned()
}

pub async fn finish_create_dag(dag_ids: &[u32]) {
    for dag_id in dag_ids {
        let dag = get_dag(*dag_id);

        if let Some(dag) = dag {
            let source_nodes = dag.get_source_nodes();
            if source_nodes.is_none() {
                panic!("DAG ID {} is not have source node", dag_id);
            }
            let sink_nodes = dag.get_sink_nodes();
            if sink_nodes.is_none() {
                panic!("DAG ID {} is not have sink node", dag_id);
            }
            if !dag.is_weakly_connected() {
                panic!("DAG ID {} is not weakly connected", dag_id);
            }
            if dag.is_cycle() {
                panic!("DAG ID {} is cycle", dag_id);
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
        } else {
            panic!("DAG ID {} is not found", dag_id);
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
        let dag_id = create_dag();
        let dag = get_dag(dag_id).unwrap();
        dag.add_node(create_node_info(1));
        dag.add_node(create_node_info(2));
        dag.add_node(create_node_info(3));

        assert_eq!(dag.node_count(), 3);
    }

    #[test]
    fn test_add_edge() {
        let dag_id = create_dag();
        let dag = get_dag(dag_id).unwrap();
        let a = dag.add_node(create_node_info(1));
        let b = dag.add_node(create_node_info(2));
        let c = dag.add_node(create_node_info(3));

        let ab = dag.add_edge(a, b);
        dag.add_edge(a, c);
        dag.add_edge(b, c);

        assert_eq!(dag.edge_count(), 3);
    }

    #[test]
    fn test_remove_node() {
        let dag_id = create_dag();
        let dag = get_dag(dag_id).unwrap();
        let a = dag.add_node(create_node_info(1));
        let b = dag.add_node(create_node_info(2));
        let c = dag.add_node(create_node_info(3));

        dag.add_edge(a, b);
        dag.add_edge(a, c);
        dag.add_edge(b, c);

        dag.remove_node(c);
        assert_eq!(dag.node_count(), 2);
        assert_eq!(dag.edge_count(), 1);
    }

    #[test]
    fn test_remove_edge() {
        let dag_id = create_dag();
        let dag = get_dag(dag_id).unwrap();
        let a = dag.add_node(create_node_info(1));
        let b = dag.add_node(create_node_info(2));

        let ab = dag.add_edge(a, b);

        assert_eq!(dag.edge_count(), 1);
        dag.remove_edge(ab);
        assert_eq!(dag.edge_count(), 0);
    }
}
