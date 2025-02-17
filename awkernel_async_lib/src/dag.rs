pub mod graph;

use alloc::{
    collections::{btree_map::Entry, BTreeMap},
    sync::Arc,
};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

static DAGS: Mutex<Dags> = Mutex::new(Dags::new()); // Set of tasks.

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

    pub fn add_edge(
        &self,
        source: graph::NodeIndex,
        target: graph::NodeIndex,
        data: u32,
    ) -> graph::EdgeIndex {
        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        graph.add_edge(source, target, data)
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

    pub fn debug_print(&self) {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        log::info!("Dag ID: {}", self.id);
        log::info!("Graph: {:#?}", *graph);
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

            // Find an unused task ID.
            if let btree_map::Entry::Vacant(e) = self.id_to_dag.entry(id) {
                let dag = Dag {
                    id,
                    graph: Mutex::new(graph::Graph::new()),
                };

                e.insert(Arc::new(dag));
                self.candidate_id = id;

                return id;
            } else {
                // The candidate task ID is already used.
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
// TODO: Implementation of API to build DAGs from Reactor
