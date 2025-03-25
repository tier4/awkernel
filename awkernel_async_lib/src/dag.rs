pub mod graph;
mod unionfind;
mod visit;

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
mod tests {
    use super::*;
    use crate::dag::graph::algo::connected_components;
    use crate::dag::graph::algo::is_cyclic_directed;

    #[test]
    fn test_connected_components() {
        let dag = create_dag();

        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);
        let num = connected_components(&*graph);
        assert_eq!(num, 0);

        let a = graph.add_node(1);
        let num = connected_components(&*graph);
        assert_eq!(num, 1);

        let b = graph.add_node(2);
        let num = connected_components(&*graph);
        assert_eq!(num, 2);

        graph.add_edge(a, b, 0);
        let num = connected_components(&*graph);
        assert_eq!(num, 1);
    }

    #[test]
    fn test_is_cyclic_directed_true() {
        let dag = create_dag();

        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);

        let a = graph.add_node(1);
        let b = graph.add_node(2);

        graph.add_edge(a, b, 0);
        graph.add_edge(b, a, 0);
        assert_eq!(is_cyclic_directed(&*graph), true);
    }

    #[test]
    fn test_is_cyclic_directed_false() {
        let dag = create_dag();

        let mut node = MCSNode::new();
        let mut graph = dag.graph.lock(&mut node);

        let a = graph.add_node(1);
        let b = graph.add_node(2);

        graph.add_edge(a, b, 0);
        assert_eq!(is_cyclic_directed(&*graph), false);
    }
}
