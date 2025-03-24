pub mod graph;

use crate::dag::graph::{direction::Direction, NodeIndex};
use alloc::{
    collections::{btree_map, BTreeMap},
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

static DAGS: Mutex<Dags> = Mutex::new(Dags::new()); // Set of DAGs.

pub struct Dag {
    pub id: u32,
    pub graph: Mutex<graph::Graph<u32, u32>>, //TODO: Change to attribute
}

impl Dag {
    #[allow(dead_code)] //TODO: Remove
    fn add_node(&self, graph: &mut graph::Graph<u32, u32>, data: u32) -> NodeIndex {
        graph.add_node(data)
    }

    #[allow(dead_code)] //TODO: Remove
    fn add_edge(
        &self,
        graph: &mut graph::Graph<u32, u32>,
        source: NodeIndex,
        target: NodeIndex,
    ) -> graph::EdgeIndex {
        graph.add_edge(source, target, 0) // 0 is the temporary weight
    }

    #[allow(dead_code)] //TODO: Remove
    fn node_count(&self, graph: &graph::Graph<u32, u32>) -> usize {
        graph.node_count()
    }

    #[allow(dead_code)] //TODO: Remove
    fn node_indices(&self, graph: &graph::Graph<u32, u32>) -> Vec<NodeIndex> {
        graph.node_indices().collect()
    }

    #[allow(dead_code)] //TODO: Remove
    fn node_weight(&self, graph: &graph::Graph<u32, u32>, node_idx: NodeIndex) -> Option<u32> {
        graph.node_weight(node_idx).cloned()
    }

    #[allow(dead_code)] //TODO: Remove
    fn neighbors_directed(
        &self,
        graph: &graph::Graph<u32, u32>,
        node_idx: NodeIndex,
        dir: Direction,
    ) -> Vec<NodeIndex> {
        graph.neighbors_directed(node_idx, dir).collect()
    }

    #[allow(dead_code)] //TODO: Remove
    fn neighbors_undirected(
        &self,
        graph: &graph::Graph<u32, u32>,
        node_idx: NodeIndex,
    ) -> Vec<NodeIndex> {
        graph.neighbors_undirected(node_idx).collect()
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

// TODO: Implementation of API to build DAGs from Reactor

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_add_node() {
        let dag = create_dag();
        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);

        dag.add_node(&mut graph, 1);
        dag.add_node(&mut graph, 2);
        dag.add_node(&mut graph, 3);

        assert_eq!(dag.node_count(&graph), 3);
    }

    #[test]
    fn test_add_edge() {
        let dag = create_dag();
        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);

        let a = dag.add_node(&mut graph, 1);
        let b = dag.add_node(&mut graph, 2);
        let c = dag.add_node(&mut graph, 3);

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

        let a = dag.add_node(&mut graph, 1);
        let b = dag.add_node(&mut graph, 2);
        let c = dag.add_node(&mut graph, 3);

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

        let a = dag.add_node(&mut graph, 1);
        let b = dag.add_node(&mut graph, 2);
        let c = dag.add_node(&mut graph, 3);
        let d = dag.add_node(&mut graph, 4);

        dag.add_edge(&mut graph, a, b);
        dag.add_edge(&mut graph, a, c);
        dag.add_edge(&mut graph, b, d);

        let neighbors = dag.neighbors_undirected(&graph, b);
        assert_eq!(neighbors.len(), 2);
        assert_eq!(neighbors.contains(&d), true);
        assert_eq!(neighbors.contains(&a), true);
    }
}
