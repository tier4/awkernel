//! Graph Module
//!
//! This file includes portions of code from petgraph under Apache License 2.0 OR the MIT License.
//!
//! Modifications include:
//! - Adapted for no-std
//! - DAG-specific adjustments
//!
//! This file is dual-licensed under the Apache License 2.0 OR the MIT License,
//! at your option. This means you can use, modify, and distribute this file under
//! either of these licenses.
//!
//! # LICENSE (Apache-2.0 OR MIT)
//!
//! ```text
//! Licensed under either of
//!
//! - Apache License, Version 2.0 (LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0)
//! - MIT License (LICENSE-MIT or https://opensource.org/licenses/MIT)
//!
//! at your option. This file may not be copied, modified, or distributed except
//! according to those terms.
//! ```
//!
//! # LICENSE (Apache-2.0)
//!
//! ```text
//! Apache License
//! Copyright 2015 bluss, github:petgraph:release-team, ABorgna
//!
//! Licensed under the Apache License, Version 2.0 (the "License");
//! you may not use this file except in compliance with the License.
//! You may obtain a copy of the License at
//!
//! http://www.apache.org/licenses/LICENSE-2.0
//!
//! Unless required by applicable law or agreed to in writing, software
//! distributed under the License is distributed on an "AS IS" BASIS,
//! WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//! See the License for the specific language governing permissions and
//! limitations under the License.
//!
//! # LICENSE (MIT)
//!
//! ```text
//! The MIT License (MIT)
//!
//! Copyright (c) 2015 bluss, github:petgraph:release-team, ABorgna
//!
//! Permission is hereby granted, free of charge, to any person obtaining a copy
//! of this software and associated documentation files (the "Software"), to deal
//! in the Software without restriction, including without limitation the rights
//! to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//! copies of the Software, and to permit persons to whom the Software is
//! furnished to do so, subject to the following conditions:
//!
//! The above copyright notice and this permission notice shall be included in all
//! copies or substantial portions of the Software.
//!
//! THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//! IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//! FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//! AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//! LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//! OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
//! SOFTWARE.
//! ```

use alloc::vec::Vec;
use core::cmp::max;
use core::fmt::{self, Debug};
use core::hash::Hash;
use core::iter;
use core::marker::PhantomData;
use core::ops::Range;
use core::slice;

pub mod algo;
pub mod direction;
mod iter_format;
use crate::dag::visit;
use direction::{Direction, Direction::Outgoing};
use fixedbitset::FixedBitSet;
use iter_format::{DebugMap, IterFormatExt, NoPretty};

macro_rules! clone_fields {
    ($name:ident, $($field:ident),+ $(,)*) => (
        fn clone(&self) -> Self {
            $name {
                $(
                    $field : self . $field .clone()
                ),*
            }
        }
    );
}

/// The default integer type for graph indices.
/// `u32` is the default to reduce the size of the graph's data and improve
/// performance in the common case.
///
/// Used for node and edge indices in `Graph`.
pub type DefaultIx = u32;

/// Trait for the unsigned integer type used for node and edge indices.
///
/// # Safety
///
/// Marked `unsafe` because: the trait must faithfully preserve
/// and convert index values.
pub unsafe trait IndexType: Copy + Default + Hash + Ord + fmt::Debug + 'static {
    fn new(x: usize) -> Self;
    fn index(&self) -> usize;
    fn max() -> Self;
}

unsafe impl IndexType for usize {
    #[inline(always)]
    fn new(x: usize) -> Self {
        x
    }
    #[inline(always)]
    fn index(&self) -> Self {
        *self
    }
    #[inline(always)]
    fn max() -> Self {
        usize::MAX
    }
}

unsafe impl IndexType for u32 {
    #[inline(always)]
    fn new(x: usize) -> Self {
        x as u32
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
    #[inline(always)]
    fn max() -> Self {
        u32::MAX
    }
}

unsafe impl IndexType for u16 {
    #[inline(always)]
    fn new(x: usize) -> Self {
        x as u16
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
    #[inline(always)]
    fn max() -> Self {
        u16::MAX
    }
}

unsafe impl IndexType for u8 {
    #[inline(always)]
    fn new(x: usize) -> Self {
        x as u8
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
    #[inline(always)]
    fn max() -> Self {
        u8::MAX
    }
}

/// Node identifier.
#[derive(Copy, Clone, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct NodeIndex<Ix = DefaultIx>(Ix);

impl<Ix: IndexType> NodeIndex<Ix> {
    #[inline]
    pub fn new(x: usize) -> Self {
        NodeIndex(IndexType::new(x))
    }

    #[inline]
    pub fn index(self) -> usize {
        self.0.index()
    }

    #[inline]
    pub fn end() -> Self {
        NodeIndex(IndexType::max())
    }

    fn _into_edge(self) -> EdgeIndex<Ix> {
        EdgeIndex(self.0)
    }
}

unsafe impl<Ix: IndexType> IndexType for NodeIndex<Ix> {
    fn index(&self) -> usize {
        self.0.index()
    }
    fn new(x: usize) -> Self {
        NodeIndex::new(x)
    }
    fn max() -> Self {
        NodeIndex(<Ix as IndexType>::max())
    }
}

impl<Ix: IndexType> From<Ix> for NodeIndex<Ix> {
    fn from(ix: Ix) -> Self {
        NodeIndex(ix)
    }
}

impl<Ix: fmt::Debug> fmt::Debug for NodeIndex<Ix> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "NodeIndex({:?})", self.0)
    }
}

/// Short version of `NodeIndex::new`
pub fn node_index<Ix: IndexType>(index: usize) -> NodeIndex<Ix> {
    NodeIndex::new(index)
}

/// Short version of `EdgeIndex::new`
pub fn edge_index<Ix: IndexType>(index: usize) -> EdgeIndex<Ix> {
    EdgeIndex::new(index)
}

/// Edge identifier.
#[derive(Copy, Clone, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct EdgeIndex<Ix = DefaultIx>(Ix);

impl<Ix: IndexType> EdgeIndex<Ix> {
    #[inline]
    pub fn new(x: usize) -> Self {
        EdgeIndex(IndexType::new(x))
    }

    #[inline]
    pub fn index(self) -> usize {
        self.0.index()
    }

    /// An invalid `EdgeIndex` used to denote absence of an edge, for example
    /// to end an adjacency list.
    #[inline]
    pub fn end() -> Self {
        EdgeIndex(IndexType::max())
    }

    fn _into_node(self) -> NodeIndex<Ix> {
        NodeIndex(self.0)
    }
}

impl<Ix: IndexType> From<Ix> for EdgeIndex<Ix> {
    fn from(ix: Ix) -> Self {
        EdgeIndex(ix)
    }
}

impl<Ix: fmt::Debug> fmt::Debug for EdgeIndex<Ix> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "EdgeIndex({:?})", self.0)
    }
}

/// The graph's node type.
#[derive(Debug)]
pub struct Node<N, Ix = DefaultIx> {
    /// Associated node data.
    pub weight: N,
    /// Next edge in outgoing and incoming edge lists.
    next: [EdgeIndex<Ix>; 2],
}

impl<E, Ix> Clone for Node<E, Ix>
where
    E: Clone,
    Ix: Copy,
{
    clone_fields!(Node, weight, next,);
}

/// The graph's edge type.
#[derive(Debug)]
pub struct Edge<E, Ix = DefaultIx> {
    /// Associated edge data.
    pub weight: E,
    /// Next edge in outgoing and incoming edge lists.
    next: [EdgeIndex<Ix>; 2],
    /// Start and End node index
    node: [NodeIndex<Ix>; 2],
}

impl<E, Ix> Clone for Edge<E, Ix>
where
    E: Clone,
    Ix: Copy,
{
    clone_fields!(Edge, weight, next, node,);
}

impl<E, Ix: IndexType> Edge<E, Ix> {
    /// Return the source node index.
    pub fn source(&self) -> NodeIndex<Ix> {
        self.node[0]
    }

    /// Return the target node index.
    pub fn target(&self) -> NodeIndex<Ix> {
        self.node[1]
    }
}

pub struct Graph<N, E, Ix = DefaultIx> {
    nodes: Vec<Node<N, Ix>>,
    edges: Vec<Edge<E, Ix>>,
}

/// The resulting cloned graph has the same graph indices as `self`.
impl<N, E, Ix: IndexType> Clone for Graph<N, E, Ix>
where
    N: Clone,
    E: Clone,
{
    fn clone(&self) -> Self {
        Graph {
            nodes: self.nodes.clone(),
            edges: self.edges.clone(),
        }
    }

    fn clone_from(&mut self, rhs: &Self) {
        self.nodes.clone_from(&rhs.nodes);
        self.edges.clone_from(&rhs.edges);
    }
}

impl<N, E, Ix> fmt::Debug for Graph<N, E, Ix>
where
    N: fmt::Debug,
    E: fmt::Debug,
    Ix: IndexType,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut fmt_struct = f.debug_struct("Graph");
        fmt_struct.field("node_count", &self.node_count());
        fmt_struct.field("edge_count", &self.edge_count());
        if self.edge_count() > 0 {
            fmt_struct.field(
                "edges",
                &self
                    .edges
                    .iter()
                    .map(|e| NoPretty((e.source().index(), e.target().index())))
                    .format(", "),
            );
        }
        // skip weights if they are ZST!
        if size_of::<N>() != 0 {
            fmt_struct.field(
                "node weights",
                &DebugMap(|| self.nodes.iter().map(|n| &n.weight).enumerate()),
            );
        }
        if size_of::<E>() != 0 {
            fmt_struct.field(
                "edge weights",
                &DebugMap(|| self.edges.iter().map(|n| &n.weight).enumerate()),
            );
        }
        fmt_struct.finish()
    }
}

enum Pair<T> {
    Both(T, T),
    One(T),
    None,
}

/// Get mutable references at index `a` and `b`.
fn index_twice<T>(slc: &mut [T], a: usize, b: usize) -> Pair<&mut T> {
    if max(a, b) >= slc.len() {
        Pair::None
    } else if a == b {
        Pair::One(&mut slc[max(a, b)])
    } else {
        // safe because a, b are in bounds and distinct
        unsafe {
            let ptr = slc.as_mut_ptr();
            let ar = &mut *ptr.add(a);
            let br = &mut *ptr.add(b);
            Pair::Both(ar, br)
        }
    }
}

impl<N, E> Graph<N, E> {
    /// Create a new `Graph` with directed edges.
    pub fn new() -> Self {
        Graph {
            nodes: Vec::new(),
            edges: Vec::new(),
        }
    }
}

impl<N, E> Default for Graph<N, E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N, E, Ix> Graph<N, E, Ix>
where
    Ix: IndexType,
{
    /// Return the number of nodes (vertices) in the graph.
    ///
    /// Computes in **O(1)** time.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Return the number of edges in the graph.
    ///
    /// Computes in **O(1)** time.
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// Add a node (also called vertex) with associated data `weight` to the graph.
    ///
    /// Computes in **O(1)** time.
    ///
    /// Return the index of the new node.
    ///
    /// **Panics** if the Graph is at the maximum number of nodes for its index
    /// type (N/A if usize).
    pub fn add_node(&mut self, weight: N) -> NodeIndex<Ix> {
        let node = Node {
            weight,
            next: [EdgeIndex::end(), EdgeIndex::end()],
        };
        let node_idx = NodeIndex::new(self.nodes.len());
        // check for max capacity, except if we use usize
        assert!(<Ix as IndexType>::max().index() == !0 || NodeIndex::end() != node_idx);
        self.nodes.push(node);
        node_idx
    }

    /// Access the weight for node `a`.
    ///
    /// If node `a` doesn't exist in the graph, return `None`.
    /// Also available with indexing syntax: `&graph[a]`.
    pub fn node_weight(&self, a: NodeIndex<Ix>) -> Option<&N> {
        self.nodes.get(a.index()).map(|n| &n.weight)
    }

    /// Access the weight for node `a`, mutably.
    ///
    /// If node `a` doesn't exist in the graph, return `None`.
    /// Also available with indexing syntax: `&mut graph[a]`.
    pub fn node_weight_mut(&mut self, a: NodeIndex<Ix>) -> Option<&mut N> {
        self.nodes.get_mut(a.index()).map(|n| &mut n.weight)
    }

    /// Add an edge from `a` to `b` to the graph, with its associated
    /// data `weight`.
    ///
    /// Return the index of the new edge.
    ///
    /// Computes in **O(1)** time.
    ///
    /// **Panics** if any of the nodes don't exist.<br>
    /// **Panics** if the Graph is at the maximum number of edges for its index
    /// type (N/A if usize).
    ///
    /// **Note:** `Graph` allows adding parallel (“duplicate”) edges. If you want
    /// to avoid this, use [`.update_edge(a, b, weight)`](#method.update_edge) instead.
    pub fn add_edge(&mut self, a: NodeIndex<Ix>, b: NodeIndex<Ix>, weight: E) -> EdgeIndex<Ix> {
        let edge_idx = EdgeIndex::new(self.edges.len());
        assert!(<Ix as IndexType>::max().index() == !0 || EdgeIndex::end() != edge_idx);
        let mut edge = Edge {
            weight,
            node: [a, b],
            next: [EdgeIndex::end(); 2],
        };
        match index_twice(&mut self.nodes, a.index(), b.index()) {
            Pair::None => panic!("Graph::add_edge: node indices out of bounds"),
            Pair::One(an) => {
                edge.next = an.next;
                an.next[0] = edge_idx;
                an.next[1] = edge_idx;
            }
            Pair::Both(an, bn) => {
                // a and b are different indices
                edge.next = [an.next[0], bn.next[1]];
                an.next[0] = edge_idx;
                bn.next[1] = edge_idx;
            }
        }
        self.edges.push(edge);
        edge_idx
    }

    /// Return an iterator of all nodes with an edge starting from `a`.
    ///
    /// - `Directed`: Outgoing edges from `a`.
    /// - `Undirected`: All edges from or to `a`.
    ///
    /// Produces an empty iterator if the node doesn't exist.<br>
    /// Iterator element type is `NodeIndex<Ix>`.
    ///
    /// Use [`.neighbors(a).detach()`][1] to get a neighbor walker that does
    /// not borrow from the graph.
    ///
    /// [1]: struct.Neighbors.html#method.detach
    pub fn neighbors(&self, a: NodeIndex<Ix>) -> Neighbors<E, Ix> {
        self.neighbors_directed(a, Outgoing)
    }

    /// Return an iterator of all neighbors that have an edge between them and
    /// `a`, in the specified direction.
    ///
    /// - `Directed`, `Outgoing`: All edges from `a`.
    /// - `Directed`, `Incoming`: All edges to `a`.
    ///
    /// Produces an empty iterator if the node doesn't exist.<br>
    /// Iterator element type is `NodeIndex<Ix>`.
    ///
    /// For a `Directed` graph, neighbors are listed in reverse order of their
    /// addition to the graph, so the most recently added edge's neighbor is
    /// listed first.
    ///
    /// Use [`.neighbors_directed(a, dir).detach()`][1] to get a neighbor walker that does
    /// not borrow from the graph.
    ///
    /// [1]: struct.Neighbors.html#method.detach
    pub fn neighbors_directed(&self, a: NodeIndex<Ix>, dir: Direction) -> Neighbors<E, Ix> {
        let mut iter = self.neighbors_undirected(a);
        let k = dir.index();
        iter.next[1 - k] = EdgeIndex::end();
        iter.skip_start = NodeIndex::end();

        iter
    }

    /// Return an iterator of all neighbors that have an edge between them and
    /// `a`, in either direction.
    ///
    /// - `Directed` : All edges from or to `a`.
    ///
    /// Produces an empty iterator if the node doesn't exist.<br>
    /// Iterator element type is `NodeIndex<Ix>`.
    ///
    /// Use [`.neighbors_undirected(a).detach()`][1] to get a neighbor walker that does
    /// not borrow from the graph.
    ///
    /// [1]: struct.Neighbors.html#method.detach
    pub fn neighbors_undirected(&self, a: NodeIndex<Ix>) -> Neighbors<E, Ix> {
        Neighbors {
            skip_start: a,
            edges: &self.edges,
            next: match self.nodes.get(a.index()) {
                None => [EdgeIndex::end(), EdgeIndex::end()],
                Some(n) => n.next,
            },
        }
    }

    /// Return an iterator over either the nodes without edges to them
    /// (`Incoming`) or from them (`Outgoing`).
    ///
    /// An *internal* node has both incoming and outgoing edges.
    /// The nodes in `.externals(Incoming)` are the source nodes and
    /// `.externals(Outgoing)` are the sinks of the graph.
    ///
    /// For a graph with undirected edges, both the sinks and the sources are
    /// just the nodes without edges.
    ///
    /// The whole iteration computes in **O(|V|)** time where V is the set of nodes.
    pub fn externals(&self, dir: Direction) -> Externals<N, Ix> {
        Externals {
            iter: self.nodes.iter().enumerate(),
            dir,
        }
    }

    /// Return an iterator over the node indices of the graph.
    pub fn node_indices(&self) -> NodeIndices<Ix> {
        NodeIndices {
            r: 0..self.node_count(),
            ty: PhantomData,
        }
    }

    /// Create an iterator over all edges, in indexed order.
    ///
    /// Iterator element type is `EdgeReference<E, Ix>`.
    pub fn edge_references(&self) -> EdgeReferences<E, Ix> {
        EdgeReferences {
            iter: self.edges.iter().enumerate(),
        }
    }
}

/// An iterator over either the nodes without edges to them or from them.
#[derive(Debug, Clone)]
pub struct Externals<'a, N: 'a, Ix: IndexType = DefaultIx> {
    iter: iter::Enumerate<slice::Iter<'a, Node<N, Ix>>>,
    dir: Direction,
}

impl<'a, N: 'a, Ix> Iterator for Externals<'a, N, Ix>
where
    Ix: IndexType,
{
    type Item = NodeIndex<Ix>;
    fn next(&mut self) -> Option<NodeIndex<Ix>> {
        let k = self.dir.index();
        loop {
            match self.iter.next() {
                None => return None,
                Some((index, node)) => {
                    if node.next[k] == EdgeIndex::end() {
                        return Some(NodeIndex::new(index));
                    } else {
                        continue;
                    }
                }
            }
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }
}

/// Iterator over the neighbors of a node.
///
/// Iterator element type is `NodeIndex<Ix>`.
#[derive(Debug)]
pub struct Neighbors<'a, E: 'a, Ix: 'a = DefaultIx> {
    /// starting node to skip over
    skip_start: NodeIndex<Ix>,
    edges: &'a [Edge<E, Ix>],
    next: [EdgeIndex<Ix>; 2],
}

impl<E, Ix> Iterator for Neighbors<'_, E, Ix>
where
    Ix: IndexType,
{
    type Item = NodeIndex<Ix>;

    fn next(&mut self) -> Option<NodeIndex<Ix>> {
        // First any outgoing edges
        match self.edges.get(self.next[0].index()) {
            None => {}
            Some(edge) => {
                self.next[0] = edge.next[0];
                return Some(edge.node[1]);
            }
        }
        // Then incoming edges
        while let Some(edge) = self.edges.get(self.next[1].index()) {
            self.next[1] = edge.next[1];
            if edge.node[0] != self.skip_start {
                return Some(edge.node[0]);
            }
        }
        None
    }
}

impl<E, Ix> Clone for Neighbors<'_, E, Ix>
where
    Ix: IndexType,
{
    clone_fields!(Neighbors, skip_start, edges, next,);
}

/// A “walker” object that can be used to step through the edge list of a node.
///
/// Created with [`.detach()`](struct.Neighbors.html#method.detach).
///
/// The walker does not borrow from the graph, so it lets you step through
/// neighbors or incident edges while also mutating graph weights.
pub struct WalkNeighbors<Ix> {
    skip_start: NodeIndex<Ix>,
    next: [EdgeIndex<Ix>; 2],
}

impl<Ix> Clone for WalkNeighbors<Ix>
where
    Ix: IndexType,
{
    fn clone(&self) -> Self {
        WalkNeighbors {
            skip_start: self.skip_start,
            next: self.next,
        }
    }
}

/// Iterator over the node indices of a graph.
#[derive(Clone, Debug)]
pub struct NodeIndices<Ix = DefaultIx> {
    r: Range<usize>,
    ty: PhantomData<fn() -> Ix>,
}

impl<Ix: IndexType> Iterator for NodeIndices<Ix> {
    type Item = NodeIndex<Ix>;

    fn next(&mut self) -> Option<Self::Item> {
        self.r.next().map(node_index)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.r.size_hint()
    }
}

impl<Ix: IndexType> DoubleEndedIterator for NodeIndices<Ix> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.r.next_back().map(node_index)
    }
}

impl<Ix: IndexType> ExactSizeIterator for NodeIndices<Ix> {}

impl<N, E, Ix> visit::NodeIndexable for Graph<N, E, Ix>
where
    Ix: IndexType,
{
    #[inline]
    fn node_bound(&self) -> usize {
        self.node_count()
    }
    #[inline]
    fn to_index(&self, ix: NodeIndex<Ix>) -> usize {
        ix.index()
    }
    #[inline]
    fn from_index(&self, ix: usize) -> Self::NodeId {
        NodeIndex::new(ix)
    }
}

impl<N, E, Ix> visit::GraphBase for Graph<N, E, Ix>
where
    Ix: IndexType,
{
    type NodeId = NodeIndex<Ix>;
    type EdgeId = EdgeIndex<Ix>;
}

impl<N, E, Ix> visit::Visitable for Graph<N, E, Ix>
where
    Ix: IndexType,
{
    type Map = FixedBitSet;
    fn visit_map(&self) -> FixedBitSet {
        FixedBitSet::with_capacity(self.node_count())
    }

    fn reset_map(&self, map: &mut Self::Map) {
        map.clear();
        map.grow(self.node_count());
    }
}

impl<'a, N, E: 'a, Ix> visit::IntoNodeIdentifiers for &'a Graph<N, E, Ix>
where
    Ix: IndexType,
{
    type NodeIdentifiers = NodeIndices<Ix>;
    fn node_identifiers(self) -> NodeIndices<Ix> {
        Graph::node_indices(self)
    }
}

impl<N, E, Ix> visit::NodeCount for Graph<N, E, Ix>
where
    Ix: IndexType,
{
    fn node_count(&self) -> usize {
        self.node_count()
    }
}

impl<N, E, Ix> visit::NodeCompactIndexable for Graph<N, E, Ix> where Ix: IndexType {}

impl<'a, N, E: 'a, Ix> visit::IntoNeighbors for &'a Graph<N, E, Ix>
where
    Ix: IndexType,
{
    type Neighbors = Neighbors<'a, E, Ix>;
    fn neighbors(self, n: NodeIndex<Ix>) -> Neighbors<'a, E, Ix> {
        Graph::neighbors(self, n)
    }
}

impl<'a, N, E, Ix> visit::IntoNodeReferences for &'a Graph<N, E, Ix>
where
    Ix: IndexType,
{
    type NodeRef = (NodeIndex<Ix>, &'a N);
    type NodeReferences = NodeReferences<'a, N, Ix>;
    fn node_references(self) -> Self::NodeReferences {
        NodeReferences {
            iter: self.nodes.iter().enumerate(),
        }
    }
}

/// Iterator over all nodes of a graph.
#[derive(Debug, Clone)]
pub struct NodeReferences<'a, N: 'a, Ix: IndexType = DefaultIx> {
    iter: iter::Enumerate<slice::Iter<'a, Node<N, Ix>>>,
}

impl<'a, N, Ix> Iterator for NodeReferences<'a, N, Ix>
where
    Ix: IndexType,
{
    type Item = (NodeIndex<Ix>, &'a N);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|(i, node)| (node_index(i), &node.weight))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<N, Ix> DoubleEndedIterator for NodeReferences<'_, N, Ix>
where
    Ix: IndexType,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter
            .next_back()
            .map(|(i, node)| (node_index(i), &node.weight))
    }
}

impl<N, Ix> ExactSizeIterator for NodeReferences<'_, N, Ix> where Ix: IndexType {}

/// Reference to a `Graph` edge.
#[derive(Debug)]
pub struct EdgeReference<'a, E: 'a, Ix = DefaultIx> {
    index: EdgeIndex<Ix>,
    node: [NodeIndex<Ix>; 2],
    weight: &'a E,
}

impl<E, Ix: IndexType> Clone for EdgeReference<'_, E, Ix> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E, Ix: IndexType> Copy for EdgeReference<'_, E, Ix> {}

impl<E, Ix: IndexType> PartialEq for EdgeReference<'_, E, Ix>
where
    E: PartialEq,
{
    fn eq(&self, rhs: &Self) -> bool {
        self.index == rhs.index && self.weight == rhs.weight
    }
}

impl<Ix, E> visit::EdgeRef for EdgeReference<'_, E, Ix>
where
    Ix: IndexType,
{
    type NodeId = NodeIndex<Ix>;
    type EdgeId = EdgeIndex<Ix>;
    type Weight = E;

    fn source(&self) -> Self::NodeId {
        self.node[0]
    }
    fn target(&self) -> Self::NodeId {
        self.node[1]
    }
    fn weight(&self) -> &E {
        self.weight
    }
    fn id(&self) -> Self::EdgeId {
        self.index
    }
}

/// Iterator over all edges of a graph.
#[derive(Debug, Clone)]
pub struct EdgeReferences<'a, E: 'a, Ix: IndexType = DefaultIx> {
    iter: iter::Enumerate<slice::Iter<'a, Edge<E, Ix>>>,
}

impl<'a, E, Ix> Iterator for EdgeReferences<'a, E, Ix>
where
    Ix: IndexType,
{
    type Item = EdgeReference<'a, E, Ix>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(i, edge)| EdgeReference {
            index: edge_index(i),
            node: edge.node,
            weight: &edge.weight,
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<E, Ix> DoubleEndedIterator for EdgeReferences<'_, E, Ix>
where
    Ix: IndexType,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(i, edge)| EdgeReference {
            index: edge_index(i),
            node: edge.node,
            weight: &edge.weight,
        })
    }
}

impl<E, Ix> ExactSizeIterator for EdgeReferences<'_, E, Ix> where Ix: IndexType {}

impl<'a, N: 'a, E: 'a, Ix> visit::IntoEdgeReferences for &'a Graph<N, E, Ix>
where
    Ix: IndexType,
{
    type EdgeRef = EdgeReference<'a, E, Ix>;
    type EdgeReferences = EdgeReferences<'a, E, Ix>;
    fn edge_references(self) -> Self::EdgeReferences {
        (*self).edge_references()
    }
}

impl<N, E, Ix> visit::Data for Graph<N, E, Ix>
where
    Ix: IndexType,
{
    type NodeWeight = N;
    type EdgeWeight = E;
}
