pub mod graph;

use alloc::{
    collections::{btree_map, BTreeMap},
    sync::Arc,
};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

static DAGS: Mutex<Dags> = Mutex::new(Dags::new()); // Set of DAGs.

pub struct Dag {
    pub id: u32,
    pub graph: Mutex<graph::Graph<u32, u32>>, //TODO: Change to attribute
}

impl Dag {
    pub fn add_node(&self, data: u32) -> graph::NodeIndex {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        graph.add_node(data)
    }

    pub fn add_edge(&self, source: graph::NodeIndex, target: graph::NodeIndex) -> graph::EdgeIndex {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        graph.add_edge(source, target, 0) // 0 is the temporary weight
    }

    pub fn remove_node(&self, node_idx: graph::NodeIndex) {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        graph.remove_node(node_idx);
    }

    pub fn remove_edge(&self, edge_idx: graph::EdgeIndex) {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        graph.remove_edge(edge_idx);
    }

    pub fn edge_endpoints(
        &self,
        edge_idx: graph::EdgeIndex,
    ) -> Option<(graph::NodeIndex, graph::NodeIndex)> {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        graph.edge_endpoints(edge_idx)
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
}

/// DAGs.
#[derive(Default)]
struct Dags {
    candidate_id: u32, // Next candidate of Dag ID.
    id_to_dag: BTreeMap<u32, Arc<Mutex<Dag>>>,
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
                };

                e.insert(Arc::new(Mutex::new(dag)));
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

pub fn get_dag(id: u32) -> Option<Arc<Mutex<Dag>>> {
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
        let dag_id = create_dag();
        let dag = get_dag(dag_id).unwrap();
        let mut node = MCSNode::new();
        let lock_dag = dag.lock(&mut node);
        lock_dag.add_node(1);
        lock_dag.add_node(2);
        lock_dag.add_node(3);

        assert_eq!(lock_dag.node_count(), 3);
    }

    #[test]
    fn test_add_edge() {
        let dag_id = create_dag();
        let dag = get_dag(dag_id).unwrap();
        let mut node = MCSNode::new();
        let lock_dag = dag.lock(&mut node);
        let a = lock_dag.add_node(1);
        let b = lock_dag.add_node(2);
        let c = lock_dag.add_node(3);

        let ab = lock_dag.add_edge(a, b);
        let _ac = lock_dag.add_edge(a, c);
        let _bc = lock_dag.add_edge(b, c);

        assert_eq!(lock_dag.edge_count(), 3);
        if let Some(ab_endpoints) = lock_dag.edge_endpoints(ab) {
            assert_eq!(ab_endpoints, (a, b));
        }
    }

    #[test]
    fn test_remove_node() {
        let dag_id = create_dag();
        let dag = get_dag(dag_id).unwrap();
        let mut node = MCSNode::new();
        let lock_dag = dag.lock(&mut node);
        let a = lock_dag.add_node(1);
        let b = lock_dag.add_node(2);
        let c = lock_dag.add_node(3);

        lock_dag.add_edge(a, b);
        lock_dag.add_edge(a, c);
        lock_dag.add_edge(b, c);

        lock_dag.remove_node(c);
        assert_eq!(lock_dag.node_count(), 2);
        assert_eq!(lock_dag.edge_count(), 1);
    }

    #[test]
    fn test_remove_edge() {
        let dag_id = create_dag();
        let dag = get_dag(dag_id).unwrap();
        let mut node = MCSNode::new();
        let lock_dag = dag.lock(&mut node);
        let a = lock_dag.add_node(1);
        let b = lock_dag.add_node(2);

        let ab = lock_dag.add_edge(a, b);

        lock_dag.remove_edge(ab);
        assert_eq!(lock_dag.edge_endpoints(ab), None);
    }
}
