#[macro_use]
mod macros;

pub mod dfsvisit;

use fixedbitset::FixedBitSet;
// use alloc::collections::BTreeSet;
// use core::hash::{BuildHasher, Hash};

// use super::EdgeType;
// use crate::dag::graph::direction::Direction;

use crate::dag::graph::IndexType;

trait_template! {
/// Base graph trait: defines the associated node identifier and
/// edge identifier types.
pub trait GraphBase {
    // FIXME: We can drop this escape/nodelegate stuff in Rust 1.18
    @escape [type NodeId]
    @escape [type EdgeId]
    @section nodelegate
    /// edge identifier
    type EdgeId: Copy + PartialEq;
    /// node identifier
    type NodeId: Copy + PartialEq;
}
}

GraphBase! {delegate_impl []}
GraphBase! {delegate_impl [['a, G], G, &'a mut G, deref]}

trait_template! {
/// Define associated data for nodes and edges
pub trait Data : GraphBase {
    @section type
    type NodeWeight;
    type EdgeWeight;
}
}

Data! {delegate_impl []}
Data! {delegate_impl [['a, G], G, &'a mut G, deref]}

/// A copyable reference to a graph.
pub trait GraphRef: Copy + GraphBase {}

impl<G> GraphRef for &G where G: GraphBase {}

trait_template! {
/// Access to the neighbors of each node
///
/// The neighbors are, depending on the graph’s edge type:
///
/// - `Directed`: All targets of edges from `a`.
/// - `Undirected`: All other endpoints of edges connected to `a`.
pub trait IntoNeighbors : GraphRef {
    @section type
    type Neighbors: Iterator<Item=Self::NodeId>;
    @section self
    /// Return an iterator of the neighbors of node `a`.
    fn neighbors(self, a: Self::NodeId) -> Self::Neighbors;
}
}

IntoNeighbors! {delegate_impl []}

/// An edge reference.
///
/// Edge references are used by traits `IntoEdges` and `IntoEdgeReferences`.
#[allow(dead_code)]
pub trait EdgeRef: Copy {
    type NodeId;
    type EdgeId;
    type Weight;
    /// The source node of the edge.
    fn source(&self) -> Self::NodeId;
    /// The target node of the edge.
    fn target(&self) -> Self::NodeId;
    /// A reference to the weight of the edge.
    fn weight(&self) -> &Self::Weight;
    /// The edge’s identifier.
    fn id(&self) -> Self::EdgeId;
}

impl<N, E> EdgeRef for (N, N, &E)
where
    N: Copy,
{
    type NodeId = N;
    type EdgeId = (N, N);
    type Weight = E;

    fn source(&self) -> N {
        self.0
    }
    fn target(&self) -> N {
        self.1
    }
    fn weight(&self) -> &E {
        self.2
    }
    fn id(&self) -> (N, N) {
        (self.0, self.1)
    }
}

trait_template! {
/// Access to the sequence of the graph’s `NodeId`s.
pub trait IntoNodeIdentifiers : GraphRef {
    @section type
    type NodeIdentifiers: Iterator<Item=Self::NodeId>;
    @section self
    fn node_identifiers(self) -> Self::NodeIdentifiers;
}
}

IntoNodeIdentifiers! {delegate_impl []}

trait_template! {
/// Access to the sequence of the graph’s edges
pub trait IntoEdgeReferences : Data + GraphRef {
    @section type
    type EdgeRef: EdgeRef<NodeId=Self::NodeId, EdgeId=Self::EdgeId,
                          Weight=Self::EdgeWeight>;
    type EdgeReferences: Iterator<Item=Self::EdgeRef>;
    @section self
    fn edge_references(self) -> Self::EdgeReferences;
}
}

IntoEdgeReferences! {delegate_impl [] }

trait_template! {
    /// The graph’s `NodeId`s map to indices
    #[allow(clippy::needless_arbitrary_self_type, dead_code)]
    pub trait NodeIndexable : GraphBase {
        @section self
        /// Return an upper bound of the node indices in the graph
        /// (suitable for the size of a bitmap).
        fn node_bound(self: &Self) -> usize;
        /// Convert `a` to an integer index.
        fn to_index(self: &Self, a: Self::NodeId) -> usize;
        /// Convert `i` to a node index. `i` must be a valid value in the graph.
        fn from_index(self: &Self, i: usize) -> Self::NodeId;
    }
}

NodeIndexable! {delegate_impl []}

trait_template! {
/// A graph with a known node count.
#[allow(clippy::needless_arbitrary_self_type, dead_code)]
pub trait NodeCount : GraphBase {
    @section self
    fn node_count(self: &Self) -> usize;
}
}

NodeCount! {delegate_impl []}

trait_template! {
/// The graph’s `NodeId`s map to indices, in a range without holes.
///
/// The graph's node identifiers correspond to exactly the indices
/// `0..self.node_bound()`.
pub trait NodeCompactIndexable : NodeIndexable + NodeCount { }
}

NodeCompactIndexable! {delegate_impl []}

/// A node reference.
pub trait NodeRef: Copy {
    type NodeId;
    type Weight;
    fn id(&self) -> Self::NodeId;
    fn weight(&self) -> &Self::Weight;
}

trait_template! {
/// Access to the sequence of the graph’s nodes
pub trait IntoNodeReferences : Data + IntoNodeIdentifiers {
    @section type
    type NodeRef: NodeRef<NodeId=Self::NodeId, Weight=Self::NodeWeight>;
    type NodeReferences: Iterator<Item=Self::NodeRef>;
    @section self
    fn node_references(self) -> Self::NodeReferences;
}
}

IntoNodeReferences! {delegate_impl []}

impl<Id> NodeRef for (Id, ())
where
    Id: Copy,
{
    type NodeId = Id;
    type Weight = ();
    fn id(&self) -> Self::NodeId {
        self.0
    }
    fn weight(&self) -> &Self::Weight {
        static DUMMY: () = ();
        &DUMMY
    }
}

impl<Id, W> NodeRef for (Id, &W)
where
    Id: Copy,
{
    type NodeId = Id;
    type Weight = W;
    fn id(&self) -> Self::NodeId {
        self.0
    }
    fn weight(&self) -> &Self::Weight {
        self.1
    }
}

/// A mapping for storing the visited status for NodeId `N`.
pub trait VisitMap<N> {
    /// Mark `a` as visited.
    ///
    /// Return **true** if this is the first visit, false otherwise.
    fn visit(&mut self, a: N) -> bool;

    /// Return whether `a` has been visited before.
    fn is_visited(&self, a: &N) -> bool;
}

impl<Ix> VisitMap<Ix> for FixedBitSet
where
    Ix: IndexType,
{
    fn visit(&mut self, x: Ix) -> bool {
        !self.put(x.index())
    }
    fn is_visited(&self, x: &Ix) -> bool {
        self.contains(x.index())
    }
}

trait_template! {
/// A graph that can create a map that tracks the visited status of its nodes.
#[allow(clippy::needless_arbitrary_self_type, dead_code)]
pub trait Visitable : GraphBase {
    @section type
    /// The associated map type
    type Map: VisitMap<Self::NodeId>;
    @section self
    /// Create a new visitor map
    fn visit_map(self: &Self) -> Self::Map;
    /// Reset the visitor map (and resize to new size of graph if needed)
    fn reset_map(self: &Self, map: &mut Self::Map);
}
}
Visitable! {delegate_impl []}
