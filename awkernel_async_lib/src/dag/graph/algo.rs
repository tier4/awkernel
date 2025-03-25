use crate::dag::unionfind::UnionFind;
use crate::dag::visit::{
    EdgeRef, IntoEdgeReferences, IntoNeighbors, IntoNodeIdentifiers, NodeCompactIndexable,
    Visitable,
};

pub fn connected_components<G>(g: G) -> usize
where
    G: NodeCompactIndexable + IntoEdgeReferences,
{
    let mut vertex_sets = UnionFind::new(g.node_bound());
    for edge in g.edge_references() {
        let (a, b) = (edge.source(), edge.target());

        // union the two vertices of the edge
        vertex_sets.union(g.to_index(a), g.to_index(b));
    }
    let mut labels = vertex_sets.into_labeling();
    labels.sort_unstable();
    labels.dedup();
    labels.len()
}

pub fn is_cyclic_directed<G>(g: G) -> bool
where
    G: IntoNodeIdentifiers + IntoNeighbors + Visitable,
{
    use crate::dag::visit::dfsvisit::{depth_first_search, DfsEvent};

    depth_first_search(g, g.node_identifiers(), |event| match event {
        DfsEvent::BackEdge(_, _) => Err(()),
        _ => Ok(()),
    })
    .is_err()
}
