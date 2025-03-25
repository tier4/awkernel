use crate::dag::visit::IntoNeighbors;
use crate::dag::visit::{VisitMap, Visitable};

/// Strictly monotonically increasing event time for a depth first search.
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Default, Hash)]
pub struct Time(pub usize);

/// A depth first search (DFS) visitor event.
#[allow(dead_code)]
#[derive(Copy, Clone, Debug)]
pub enum DfsEvent<N> {
    Discover(N, Time),
    /// An edge of the tree formed by the traversal.
    TreeEdge(N, N),
    /// An edge to an already visited node.
    BackEdge(N, N),
    /// A cross or forward edge.
    ///
    /// For an edge *(u, v)*, if the discover time of *v* is greater than *u*,
    /// then it is a forward edge, else a cross edge.
    CrossForwardEdge(N, N),
    /// All edges from a node have been reported.
    Finish(N, Time),
}

/// Return if the expression is a break value, execute the provided statement
/// if it is a prune value.
macro_rules! try_control {
    ($e:expr, $p:stmt) => {
        try_control!($e, $p, ());
    };
    ($e:expr, $p:stmt, $q:stmt) => {
        match $e {
            x => {
                if x.should_break() {
                    return x;
                } else if x.should_prune() {
                    $p
                } else {
                    $q
                }
            }
        }
    };
}

/// Control flow for `depth_first_search` callbacks.
#[allow(dead_code)]
#[derive(Copy, Clone, Debug)]
pub enum Control<B> {
    /// Continue the DFS traversal as normal.
    Continue,
    /// Prune the current node from the DFS traversal. No more edges from this
    /// node will be reported to the callback. A `DfsEvent::Finish` for this
    /// node will still be reported. This can be returned in response to any
    /// `DfsEvent`, except `Finish`, which will panic.
    Prune,
    /// Stop the DFS traversal and return the provided value.
    Break(B),
}

#[allow(dead_code)]
impl<B> Control<B> {
    pub fn breaking() -> Control<()> {
        Control::Break(())
    }
    /// Get the value in `Control::Break(_)`, if present.
    pub fn break_value(self) -> Option<B> {
        match self {
            Control::Continue | Control::Prune => None,
            Control::Break(b) => Some(b),
        }
    }
}

/// Control flow for callbacks.
///
/// The empty return value `()` is equivalent to continue.
pub trait ControlFlow {
    fn continuing() -> Self;
    fn should_break(&self) -> bool;
    fn should_prune(&self) -> bool;
}

impl ControlFlow for () {
    fn continuing() {}
    #[inline]
    fn should_break(&self) -> bool {
        false
    }
    #[inline]
    fn should_prune(&self) -> bool {
        false
    }
}

impl<B> ControlFlow for Control<B> {
    fn continuing() -> Self {
        Control::Continue
    }
    fn should_break(&self) -> bool {
        matches!(*self, Control::Break(_))
    }
    fn should_prune(&self) -> bool {
        matches!(*self, Control::Prune)
    }
}

impl<C: ControlFlow, E> ControlFlow for Result<C, E> {
    fn continuing() -> Self {
        Ok(C::continuing())
    }
    fn should_break(&self) -> bool {
        if let Ok(ref c) = *self {
            c.should_break()
        } else {
            true
        }
    }
    fn should_prune(&self) -> bool {
        if let Ok(ref c) = *self {
            c.should_prune()
        } else {
            false
        }
    }
}

/// The default is `Continue`.
impl<B> Default for Control<B> {
    fn default() -> Self {
        Control::Continue
    }
}

/// A recursive depth first search.
///
/// Starting points are the nodes in the iterator `starts` (specify just one
/// start vertex *x* by using `Some(x)`).
///
/// The traversal emits discovery and finish events for each reachable vertex,
/// and edge classification of each reachable edge. `visitor` is called for each
/// event, see [`DfsEvent`][de] for possible values.
///
/// The return value should implement the trait `ControlFlow`, and can be used to change
/// the control flow of the search.
///
/// `Control` Implements `ControlFlow` such that `Control::Continue` resumes the search.
/// `Control::Break` will stop the visit early, returning the contained value.
/// `Control::Prune` will stop traversing any additional edges from the current
/// node and proceed immediately to the `Finish` event.
///
/// There are implementations of `ControlFlow` for `()`, and `Result<C, E>` where
/// `C: ControlFlow`. The implementation for `()` will continue until finished.
/// For `Result`, upon encountering an `E` it will break, otherwise acting the same as `C`.
///
/// ***Panics** if you attempt to prune a node from its `Finish` event.
pub fn depth_first_search<G, I, F, C>(graph: G, starts: I, mut visitor: F) -> C
where
    G: IntoNeighbors + Visitable,
    I: IntoIterator<Item = G::NodeId>,
    F: FnMut(DfsEvent<G::NodeId>) -> C,
    C: ControlFlow,
{
    let time = &mut Time(0);
    let discovered = &mut graph.visit_map();
    let finished = &mut graph.visit_map();

    for start in starts {
        try_control!(
            dfs_visitor(graph, start, &mut visitor, discovered, finished, time),
            unreachable!()
        );
    }
    C::continuing()
}

pub(crate) fn dfs_visitor<G, F, C>(
    graph: G,
    u: G::NodeId,
    visitor: &mut F,
    discovered: &mut impl VisitMap<G::NodeId>,
    finished: &mut impl VisitMap<G::NodeId>,
    time: &mut Time,
) -> C
where
    G: IntoNeighbors + Visitable,
    F: FnMut(DfsEvent<G::NodeId>) -> C,
    C: ControlFlow,
{
    if !discovered.visit(u) {
        return C::continuing();
    }

    try_control!(
        visitor(DfsEvent::Discover(u, time_post_inc(time))),
        {},
        for v in graph.neighbors(u) {
            if !discovered.is_visited(&v) {
                try_control!(visitor(DfsEvent::TreeEdge(u, v)), continue);
                try_control!(
                    dfs_visitor(graph, v, visitor, discovered, finished, time),
                    unreachable!()
                );
            } else if !finished.is_visited(&v) {
                try_control!(visitor(DfsEvent::BackEdge(u, v)), continue);
            } else {
                try_control!(visitor(DfsEvent::CrossForwardEdge(u, v)), continue);
            }
        }
    );
    let first_finish = finished.visit(u);
    debug_assert!(first_finish);
    try_control!(
        visitor(DfsEvent::Finish(u, time_post_inc(time))),
        panic!("Pruning on the `DfsEvent::Finish` is not supported!")
    );
    C::continuing()
}

fn time_post_inc(x: &mut Time) -> Time {
    let v = *x;
    x.0 += 1;
    v
}
