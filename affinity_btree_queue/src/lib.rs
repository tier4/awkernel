//! Affinity-aware priority queue backed by an augmented classical (CLRS-style) B-tree.
//!
//! Each entry carries `(priority, affinity: CpuMask, value)`. The tree is ordered
//! solely by `PriorityKey<P> = (priority, seq)`, where `seq` is a unique tie-breaker.
//! Every node stores `subtree_affinity`, the OR of all entry affinities in its
//! subtree, which lets `peek_key_for_cpu`/`pop_for_cpu` skip subtrees with no
//! entry runnable on the requested CPU. Smaller priority value = higher priority;
//! wrap with `core::cmp::Reverse` for the opposite order.
//!
//! # Quick start
//!
//! ```
//! use affinity_btree_queue::{AffinityBTreeQueue, CpuMask};
//!
//! // Create a queue for a 4-CPU system.
//! // Smaller priority value = higher priority.
//! // Use `core::cmp::Reverse` if you want larger values to dequeue first.
//! let mut q: AffinityBTreeQueue<u32, &str> = AffinityBTreeQueue::new(4);
//!
//! // Build CPU affinity masks.
//! let mut cpu0 = CpuMask::empty();
//! cpu0.insert(0);
//!
//! let mut cpu12 = CpuMask::empty();
//! cpu12.insert(1);
//! cpu12.insert(2);
//!
//! let mut all = CpuMask::empty();
//! for c in 0..4 { all.insert(c); }
//!
//! // push returns a PriorityKey handle that can be passed to remove() later.
//! q.push(10, all,   "low priority, any CPU").unwrap();
//! q.push(5,  cpu12, "medium, CPUs 1-2 only").unwrap();
//! q.push(1,  cpu0,  "high priority, CPU 0 only").unwrap();
//!
//! // pop_for_cpu(cpu) returns the highest-priority (lowest value) entry
//! // whose affinity includes the given CPU.
//! let (_, _, v) = q.pop_for_cpu(0).unwrap();
//! assert_eq!(v, "high priority, CPU 0 only"); // priority=1
//!
//! // The cpu12 entry (priority=5) is not runnable on CPU 0, so priority=10 is next.
//! let (_, _, v) = q.pop_for_cpu(0).unwrap();
//! assert_eq!(v, "low priority, any CPU");     // priority=10
//!
//! // CPU 1 can run the cpu12 entry (priority=5).
//! let (_, _, v) = q.pop_for_cpu(1).unwrap();
//! assert_eq!(v, "medium, CPUs 1-2 only");     // priority=5
//! ```
//!
//! # Max-first ordering with `Reverse`
//!
//! ```
//! use affinity_btree_queue::{AffinityBTreeQueue, CpuMask};
//! use core::cmp::Reverse;
//!
//! let mut q: AffinityBTreeQueue<Reverse<u32>, u32> = AffinityBTreeQueue::new(1);
//! let mut m = CpuMask::empty();
//! m.insert(0);
//! q.push(Reverse(1),   m, 1).unwrap();
//! q.push(Reverse(100), m, 100).unwrap();
//!
//! // Reverse(100) < Reverse(1), so the numerically larger value dequeues first.
//! let (_, _, v) = q.pop_for_cpu(0).unwrap();
//! assert_eq!(v, 100);
//! ```

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

use alloc::vec::Vec;
use core::cmp::Ordering;
use core::mem;

/// Default B-tree minimum degree for production builds.
pub const DEFAULT_MIN_DEGREE: usize = 16;

/// Sequence number type used as a unique tie-breaker for entries with the same
/// priority.
pub type Seq = u64;

/// CPU affinity bitmask backed by `N` 64-bit words, supporting up to `N * 64`
/// CPUs. `CpuMask<1>` (the default) supports up to 64 CPUs; `CpuMask<2>`
/// supports up to 128, etc.
///
/// All constructors and bit operations are `const fn`, so masks can be built
/// in `const`/`static` initializers with the chainable [`with`](Self::with)
/// builder.
///
/// # Examples
///
/// ```
/// use affinity_btree_queue::CpuMask;
///
/// let mut m: CpuMask = CpuMask::empty();
/// m.insert(0);
/// m.insert(3);
/// assert!(m.contains(0));
/// assert!(m.contains(3));
/// assert!(!m.contains(1));
///
/// // Construct directly from a bitmask.
/// let m2: CpuMask = CpuMask::from_bits_truncate(0b1001); // CPU 0 and 3
/// assert_eq!(m, m2);
///
/// // Construct in a const context.
/// const M3: CpuMask = CpuMask::empty().with(0).with(3);
/// assert_eq!(M3, m);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CpuMask<const N: usize = 1>([u64; N]);

impl<const N: usize> CpuMask<N> {
    pub const fn empty() -> Self {
        CpuMask([0u64; N])
    }

    /// Creates a mask with all `N * 64` bits set.
    ///
    /// Combine with [`masked_below`](Self::masked_below) to build "all CPUs
    /// of an `n`-CPU system" masks.
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::CpuMask;
    /// let m: CpuMask<2> = CpuMask::all();
    /// assert!(m.contains(0));
    /// assert!(m.contains(127));
    /// ```
    pub const fn all() -> Self {
        CpuMask([u64::MAX; N])
    }

    pub const fn is_empty(self) -> bool {
        let mut i = 0;
        while i < N {
            if self.0[i] != 0 {
                return false;
            }
            i += 1;
        }
        true
    }

    pub const fn contains(self, cpu: usize) -> bool {
        let word = cpu / 64;
        let bit = cpu % 64;
        word < N && (self.0[word] >> bit) & 1 == 1
    }

    pub const fn union(self, other: Self) -> Self {
        let mut result = [0u64; N];
        let mut i = 0;
        while i < N {
            result[i] = self.0[i] | other.0[i];
            i += 1;
        }
        CpuMask(result)
    }

    /// Sets the bit for `cpu`. Panics if `cpu >= N * 64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::CpuMask;
    /// let mut m: CpuMask = CpuMask::empty();
    /// m.insert(0);
    /// m.insert(63);
    /// assert!(m.contains(0));
    /// assert!(m.contains(63));
    /// assert!(!m.contains(1));
    /// ```
    pub const fn insert(&mut self, cpu: usize) {
        assert!(cpu < N * 64, "CPU index out of CpuMask range");
        self.0[cpu / 64] |= 1u64 << (cpu % 64);
    }

    /// Clears the bit for `cpu`. Panics if `cpu >= N * 64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::CpuMask;
    /// let mut m: CpuMask = CpuMask::from_bits_truncate(0b11);
    /// m.remove(0);
    /// assert!(!m.contains(0));
    /// assert!(m.contains(1));
    /// ```
    pub const fn remove(&mut self, cpu: usize) {
        assert!(cpu < N * 64, "CPU index out of CpuMask range");
        self.0[cpu / 64] &= !(1u64 << (cpu % 64));
    }

    /// Chainable version of [`insert`](Self::insert): returns a copy of the
    /// mask with the bit for `cpu` set. Panics if `cpu >= N * 64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::CpuMask;
    /// const M: CpuMask = CpuMask::empty().with(1).with(2);
    /// assert!(!M.contains(0));
    /// assert!(M.contains(1));
    /// assert!(M.contains(2));
    /// ```
    pub const fn with(mut self, cpu: usize) -> Self {
        self.insert(cpu);
        self
    }

    /// Chainable version of [`remove`](Self::remove): returns a copy of the
    /// mask with the bit for `cpu` cleared. Panics if `cpu >= N * 64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::CpuMask;
    /// const M: CpuMask = CpuMask::all().without(0);
    /// assert!(!M.contains(0));
    /// assert!(M.contains(1));
    /// ```
    pub const fn without(mut self, cpu: usize) -> Self {
        self.remove(cpu);
        self
    }

    /// Returns a copy of the mask with every bit at index `>= n` cleared,
    /// keeping only CPUs `0..n`.
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::CpuMask;
    /// let m: CpuMask<2> = CpuMask::all().masked_below(65);
    /// assert!(m.contains(64));
    /// assert!(!m.contains(65));
    /// assert_eq!(m.word(0), u64::MAX);
    /// assert_eq!(m.word(1), 1);
    /// ```
    pub const fn masked_below(mut self, n: usize) -> Self {
        let mut i = 0;
        while i < N {
            let lo = i * 64;
            if lo >= n {
                self.0[i] = 0;
            } else {
                let valid = n - lo; // 1..=64 bits of this word are valid.
                if valid < 64 {
                    self.0[i] &= (1u64 << valid) - 1;
                }
            }
            i += 1;
        }
        self
    }

    /// Creates a mask with word 0 set to `bits` and all other words zeroed.
    /// For `N = 1`, this is equivalent to setting the full mask.
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::CpuMask;
    /// // Set bits for CPU 0 and CPU 2.
    /// let m: CpuMask = CpuMask::from_bits_truncate(0b0101);
    /// assert!(m.contains(0));
    /// assert!(!m.contains(1));
    /// assert!(m.contains(2));
    /// ```
    pub const fn from_bits_truncate(bits: u64) -> Self {
        let mut result = [0u64; N];
        if N > 0 {
            result[0] = bits;
        }
        CpuMask(result)
    }

    /// Returns word 0 of the mask as a `u64`.
    /// For `N = 1`, this is the full mask.
    pub const fn bits(self) -> u64 {
        if N > 0 { self.0[0] } else { 0 }
    }

    /// Returns word `idx` of the backing array. Panics if `idx >= N`.
    pub const fn word(self, idx: usize) -> u64 {
        self.0[idx]
    }

    /// Sets word `idx` of the backing array. Panics if `idx >= N`.
    pub const fn set_word(&mut self, idx: usize, bits: u64) {
        self.0[idx] = bits;
    }

    /// Iterates over the CPU indices contained in the mask, in ascending
    /// order. Cost is O(number of set bits): zero words are skipped in one
    /// step and each set bit is located with `trailing_zeros`.
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::CpuMask;
    /// let m: CpuMask<2> = CpuMask::empty().with(1).with(63).with(64).with(100);
    /// let cpus: Vec<usize> = m.iter().collect();
    /// assert_eq!(cpus, [1, 63, 64, 100]);
    /// ```
    pub fn iter(self) -> impl Iterator<Item = usize> {
        (0..N).flat_map(move |w| {
            let mut word = self.0[w];
            core::iter::from_fn(move || {
                if word == 0 {
                    return None;
                }
                let bit = word.trailing_zeros() as usize;
                word &= word - 1; // Clear the lowest set bit.
                Some(w * 64 + bit)
            })
        })
    }

    /// True if no bit at index >= `num_cpus` is set.
    fn fits_within(self, num_cpus: usize) -> bool {
        if num_cpus >= N * 64 {
            return true;
        }
        let full_words = num_cpus / 64;
        let extra_bits = num_cpus % 64;
        let upper_start = if extra_bits > 0 {
            full_words + 1
        } else {
            full_words
        };
        for i in upper_start..N {
            if self.0[i] != 0 {
                return false;
            }
        }
        if extra_bits > 0 && full_words < N && self.0[full_words] >> extra_bits != 0 {
            return false;
        }
        true
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PushError {
    EmptyAffinity,
    SequenceOverflow,
    InvalidCpu,
}

/// Unique B-tree key: ordered by `(priority, seq)` lexicographically.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PriorityKey<P> {
    pub priority: P,
    pub seq: Seq,
}

impl<P: Ord> Ord for PriorityKey<P> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.priority
            .cmp(&other.priority)
            .then_with(|| self.seq.cmp(&other.seq))
    }
}

impl<P: Ord> PartialOrd for PriorityKey<P> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug)]
struct Entry<P, V, const N: usize> {
    key: PriorityKey<P>,
    affinity: CpuMask<N>,
    value: V,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct NodeId(usize);

#[derive(Debug)]
struct Node<P, V, const N: usize> {
    leaf: bool,
    entries: Vec<Entry<P, V, N>>,
    // Empty when leaf; otherwise children.len() == entries.len() + 1.
    children: Vec<NodeId>,
    // OR of all affinities in this node and its descendants.
    subtree_affinity: CpuMask<N>,
}

/// First index in `entries` whose key is >= `key`.
fn lower_bound<P: Ord, V, const N: usize>(
    entries: &[Entry<P, V, N>],
    key: &PriorityKey<P>,
) -> usize {
    let mut lo = 0;
    let mut hi = entries.len();
    while lo < hi {
        let mid = (lo + hi) / 2;
        if entries[mid].key < *key {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

/// Affinity-aware priority queue over an augmented classical B-tree of
/// minimum degree `T` (`MIN_KEYS = T - 1`, `MAX_KEYS = 2 * T - 1`).
///
/// `N` is the number of 64-bit words in the CPU mask; the default `N = 1`
/// supports up to 64 CPUs. Use `N = 2` for up to 128 CPUs, etc.
pub struct AffinityBTreeQueue<P, V, const T: usize = DEFAULT_MIN_DEGREE, const N: usize = 1> {
    root: Option<NodeId>,
    // Arena with stable ids; never compacted. Freed slots go to `free_list`.
    nodes: Vec<Option<Node<P, V, N>>>,
    free_list: Vec<NodeId>,
    len: usize,
    next_seq: Seq,
    num_cpus: usize,
}

impl<P: Ord + Clone, V, const T: usize, const N: usize> AffinityBTreeQueue<P, V, T, N> {
    // Only referenced by the test invariant checker.
    #[cfg_attr(not(test), allow(dead_code))]
    const MIN_KEYS: usize = T - 1;
    const MAX_KEYS: usize = 2 * T - 1;

    /// Creates an empty queue for CPUs `0..num_cpus`. Panics if `T < 2` or
    /// `num_cpus > N * 64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::AffinityBTreeQueue;
    ///
    /// // Default degree T=16, supports up to 64 CPUs (N=1).
    /// let q: AffinityBTreeQueue<u32, ()> = AffinityBTreeQueue::new(8);
    /// assert_eq!(q.num_cpus(), 8);
    /// assert!(q.is_empty());
    /// ```
    pub fn new(num_cpus: usize) -> Self {
        assert!(T >= 2, "B-tree minimum degree T must be at least 2");
        assert!(num_cpus <= N * 64, "num_cpus exceeds CpuMask capacity N*64");
        Self {
            root: None,
            nodes: Vec::new(),
            free_list: Vec::new(),
            len: 0,
            next_seq: 0,
            num_cpus,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn num_cpus(&self) -> usize {
        self.num_cpus
    }

    /// Returns the OR of the affinities of all entries currently in the
    /// queue, i.e. the set of CPUs for which at least one entry is eligible.
    /// O(1): reads the root node's aggregated `subtree_affinity`.
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::{AffinityBTreeQueue, CpuMask};
    ///
    /// let mut q: AffinityBTreeQueue<u32, ()> = AffinityBTreeQueue::new(4);
    /// assert!(q.affinity_mask().is_empty());
    ///
    /// q.push(1, CpuMask::empty().with(1), ()).unwrap();
    /// q.push(2, CpuMask::empty().with(3), ()).unwrap();
    /// assert_eq!(q.affinity_mask(), CpuMask::empty().with(1).with(3));
    ///
    /// q.pop_for_cpu(1).unwrap();
    /// assert_eq!(q.affinity_mask(), CpuMask::empty().with(3));
    /// ```
    pub fn affinity_mask(&self) -> CpuMask<N> {
        match self.root {
            Some(r) => self.node(r).subtree_affinity,
            None => CpuMask::empty(),
        }
    }

    fn node(&self, id: NodeId) -> &Node<P, V, N> {
        self.nodes[id.0].as_ref().expect("dangling NodeId")
    }

    fn node_mut(&mut self, id: NodeId) -> &mut Node<P, V, N> {
        self.nodes[id.0].as_mut().expect("dangling NodeId")
    }

    fn alloc_node(&mut self, leaf: bool) -> NodeId {
        let node = Node {
            leaf,
            entries: Vec::new(),
            children: Vec::new(),
            subtree_affinity: CpuMask::empty(),
        };
        if let Some(id) = self.free_list.pop() {
            debug_assert!(self.nodes[id.0].is_none());
            self.nodes[id.0] = Some(node);
            id
        } else {
            let id = NodeId(self.nodes.len());
            self.nodes.push(Some(node));
            id
        }
    }

    fn free_node(&mut self, id: NodeId) {
        let taken = self.nodes[id.0].take();
        debug_assert!(taken.is_some());
        self.free_list.push(id);
    }

    /// Recomputes `subtree_affinity` of `id` from its entries and children.
    /// Must be called after every mutation of a node's entries or children.
    fn pull(&mut self, id: NodeId) {
        let mut mask = CpuMask::empty();
        {
            let x = self.node(id);
            for e in &x.entries {
                mask = mask.union(e.affinity);
            }
            for &c in &x.children {
                mask = mask.union(self.node(c).subtree_affinity);
            }
        }
        self.node_mut(id).subtree_affinity = mask;
    }

    /// Inserts an entry with the given `priority`, CPU `affinity`, and `value`.
    ///
    /// Returns a [`PriorityKey`] handle that uniquely identifies the entry and
    /// can be passed to [`remove`](Self::remove) later.
    ///
    /// # Errors
    ///
    /// - [`PushError::EmptyAffinity`] — `affinity` has no bits set.
    /// - [`PushError::InvalidCpu`] — `affinity` has a bit set for a CPU ≥ `num_cpus`.
    /// - [`PushError::SequenceOverflow`] — internal sequence counter wrapped
    ///   (requires 2⁶⁴ prior pushes; practically impossible).
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::{AffinityBTreeQueue, CpuMask, PushError};
    ///
    /// let mut q: AffinityBTreeQueue<u32, u32> = AffinityBTreeQueue::new(4);
    ///
    /// let mut m = CpuMask::empty();
    /// m.insert(0);
    /// let _key = q.push(10, m, 42).unwrap();
    /// assert_eq!(q.len(), 1);
    ///
    /// // Empty affinity mask is rejected.
    /// assert_eq!(q.push(1, CpuMask::empty(), 0), Err(PushError::EmptyAffinity));
    ///
    /// // CPU 4 is out of range for a 4-CPU queue.
    /// let mut bad = CpuMask::empty();
    /// bad.insert(4);
    /// assert_eq!(q.push(1, bad, 0), Err(PushError::InvalidCpu));
    /// ```
    pub fn push(
        &mut self,
        priority: P,
        affinity: CpuMask<N>,
        value: V,
    ) -> Result<PriorityKey<P>, PushError> {
        if affinity.is_empty() {
            return Err(PushError::EmptyAffinity);
        }
        if !affinity.fits_within(self.num_cpus) {
            return Err(PushError::InvalidCpu);
        }
        let seq = self.next_seq;
        let next_seq = seq.checked_add(1).ok_or(PushError::SequenceOverflow)?;
        self.next_seq = next_seq;

        let key = PriorityKey { priority, seq };
        let ret = key.clone();
        let entry = Entry {
            key,
            affinity,
            value,
        };

        match self.root {
            None => {
                let r = self.alloc_node(true);
                self.node_mut(r).entries.push(entry);
                self.pull(r);
                self.root = Some(r);
            }
            Some(r) => {
                if self.node(r).entries.len() == Self::MAX_KEYS {
                    let s = self.alloc_node(false);
                    self.node_mut(s).children.push(r);
                    self.root = Some(s);
                    self.split_child(s, 0);
                    self.insert_non_full(s, entry);
                } else {
                    self.insert_non_full(r, entry);
                }
            }
        }
        self.len += 1;
        Ok(ret)
    }

    /// Splits the full child `parent.children[index]` around its median entry.
    fn split_child(&mut self, parent_id: NodeId, index: usize) {
        let y_id = self.node(parent_id).children[index];
        let y_leaf = self.node(y_id).leaf;
        let z_id = self.alloc_node(y_leaf);

        let (median, right_entries, right_children) = {
            let y = self.node_mut(y_id);
            debug_assert_eq!(y.entries.len(), Self::MAX_KEYS);
            let right_entries = y.entries.split_off(T);
            let median = y.entries.pop().expect("full node has a median");
            let right_children = if y_leaf {
                Vec::new()
            } else {
                y.children.split_off(T)
            };
            (median, right_entries, right_children)
        };

        {
            let z = self.node_mut(z_id);
            z.entries = right_entries;
            z.children = right_children;
        }
        {
            let p = self.node_mut(parent_id);
            p.entries.insert(index, median);
            p.children.insert(index + 1, z_id);
        }

        self.pull(y_id);
        self.pull(z_id);
        self.pull(parent_id);
    }

    fn insert_non_full(&mut self, node_id: NodeId, entry: Entry<P, V, N>) {
        debug_assert!(self.node(node_id).entries.len() < Self::MAX_KEYS);

        if self.node(node_id).leaf {
            let i = lower_bound(&self.node(node_id).entries, &entry.key);
            debug_assert!(
                i >= self.node(node_id).entries.len()
                    || self.node(node_id).entries[i].key != entry.key,
                "duplicate key"
            );
            self.node_mut(node_id).entries.insert(i, entry);
            self.pull(node_id);
            return;
        }

        let mut i = lower_bound(&self.node(node_id).entries, &entry.key);
        let child_id = self.node(node_id).children[i];
        if self.node(child_id).entries.len() == Self::MAX_KEYS {
            self.split_child(node_id, i);
            if entry.key > self.node(node_id).entries[i].key {
                i += 1;
            } else {
                debug_assert!(
                    entry.key != self.node(node_id).entries[i].key,
                    "duplicate key"
                );
            }
        }
        let next_child = self.node(node_id).children[i];
        self.insert_non_full(next_child, entry);
        self.pull(node_id);
    }

    /// Smallest key whose affinity contains `cpu`, or `None`.
    ///
    /// Does not remove the entry; use [`pop_for_cpu`](Self::pop_for_cpu) to
    /// remove it.
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::{AffinityBTreeQueue, CpuMask};
    ///
    /// let mut q: AffinityBTreeQueue<u32, u32> = AffinityBTreeQueue::new(2);
    /// assert_eq!(q.peek_key_for_cpu(0), None); // empty queue
    ///
    /// let mut m = CpuMask::empty();
    /// m.insert(1); // CPU 1 only
    /// let key = q.push(5, m, 99).unwrap();
    ///
    /// assert_eq!(q.peek_key_for_cpu(1), Some(key.clone())); // visible on CPU 1
    /// assert_eq!(q.peek_key_for_cpu(0), None);              // not visible on CPU 0
    /// assert_eq!(q.len(), 1);                               // entry was not consumed
    /// ```
    pub fn peek_key_for_cpu(&self, cpu: usize) -> Option<PriorityKey<P>> {
        if cpu >= self.num_cpus {
            return None;
        }
        let r = self.root?;
        if !self.node(r).subtree_affinity.contains(cpu) {
            return None;
        }
        Some(self.find_first_eligible_key(r, cpu))
    }

    /// Precondition: `node(node_id).subtree_affinity.contains(cpu)`.
    /// Scans in logical order child[0], entry[0], child[1], ... so the first
    /// eligible entry found is the minimum eligible key in the subtree.
    fn find_first_eligible_key(&self, node_id: NodeId, cpu: usize) -> PriorityKey<P> {
        let mut cur = node_id;

        'descend: loop {
            let x = self.node(cur);
            debug_assert!(x.subtree_affinity.contains(cpu));
            let n = x.entries.len();

            for i in 0..n {
                if !x.leaf {
                    let child_id = x.children[i];
                    if self.node(child_id).subtree_affinity.contains(cpu) {
                        cur = child_id;
                        continue 'descend;
                    }
                }
                if x.entries[i].affinity.contains(cpu) {
                    return x.entries[i].key.clone();
                }
            }

            if !x.leaf {
                let child_id = x.children[n];
                if self.node(child_id).subtree_affinity.contains(cpu) {
                    cur = child_id;
                    continue 'descend;
                }
            }

            panic!("subtree_affinity invariant is broken");
        }
    }

    /// Removes and returns the highest-priority entry runnable on `cpu`.
    ///
    /// Returns `None` if the queue is empty or no entry's affinity includes
    /// `cpu`.
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::{AffinityBTreeQueue, CpuMask};
    ///
    /// let mut q: AffinityBTreeQueue<u32, &str> = AffinityBTreeQueue::new(2);
    ///
    /// let mut cpu0 = CpuMask::empty();
    /// cpu0.insert(0);
    /// let mut cpu1 = CpuMask::empty();
    /// cpu1.insert(1);
    ///
    /// q.push(1, cpu0, "only cpu0").unwrap();
    /// q.push(2, cpu1, "only cpu1").unwrap();
    ///
    /// // CPU 0 only dequeues its own entry.
    /// let (_, affinity, value) = q.pop_for_cpu(0).unwrap();
    /// assert_eq!(value, "only cpu0");
    /// assert!(affinity.contains(0));
    ///
    /// // No more entries runnable on CPU 0.
    /// assert!(q.pop_for_cpu(0).is_none());
    /// ```
    pub fn pop_for_cpu(&mut self, cpu: usize) -> Option<(PriorityKey<P>, CpuMask<N>, V)> {
        let key = self.peek_key_for_cpu(cpu)?;
        let removed = self.remove(&key);
        debug_assert!(removed.is_some());
        debug_assert!(removed.as_ref().is_none_or(|(_, a, _)| a.contains(cpu)));
        removed
    }

    /// Removes the entry identified by `key` and returns `(key, affinity, value)`,
    /// or `None` if no such entry exists.
    ///
    /// The key is obtained from [`push`](Self::push) or
    /// [`peek_key_for_cpu`](Self::peek_key_for_cpu).
    ///
    /// # Examples
    ///
    /// ```
    /// use affinity_btree_queue::{AffinityBTreeQueue, CpuMask};
    ///
    /// let mut q: AffinityBTreeQueue<u32, u32> = AffinityBTreeQueue::new(1);
    /// let mut m = CpuMask::empty();
    /// m.insert(0);
    ///
    /// let key = q.push(7, m, 42).unwrap();
    /// let (k, _, v) = q.remove(&key).unwrap();
    /// assert_eq!(k, key);
    /// assert_eq!(v, 42);
    ///
    /// // Removing the same key a second time returns None.
    /// assert!(q.remove(&key).is_none());
    /// ```
    pub fn remove(&mut self, key: &PriorityKey<P>) -> Option<(PriorityKey<P>, CpuMask<N>, V)> {
        let root = self.root?;
        let removed = self.delete_from_node(root, key);

        if let Some(r) = self.root
            && self.node(r).entries.is_empty()
        {
            if self.node(r).leaf {
                self.free_node(r);
                self.root = None;
            } else {
                let new_root = self.node(r).children[0];
                self.free_node(r);
                self.root = Some(new_root);
            }
        }

        if removed.is_some() {
            self.len -= 1;
        }
        removed.map(|e| (e.key, e.affinity, e.value))
    }

    fn delete_from_node(
        &mut self,
        node_id: NodeId,
        key: &PriorityKey<P>,
    ) -> Option<Entry<P, V, N>> {
        let i = lower_bound(&self.node(node_id).entries, key);
        let leaf = self.node(node_id).leaf;
        let found_here =
            i < self.node(node_id).entries.len() && self.node(node_id).entries[i].key == *key;

        if found_here {
            if leaf {
                let entry = self.node_mut(node_id).entries.remove(i);
                self.pull(node_id);
                Some(entry)
            } else {
                let removed = self.delete_internal_entry(node_id, i);
                self.pull(node_id);
                removed
            }
        } else if leaf {
            None
        } else {
            let child_index = self.ensure_child_has_at_least_t(node_id, i);
            let child_id = self.node(node_id).children[child_index];
            let removed = self.delete_from_node(child_id, key);
            self.pull(node_id);
            removed
        }
    }

    /// Deletes `entries[index]` of the internal node `node_id` using the
    /// standard predecessor / successor / merge cases.
    fn delete_internal_entry(&mut self, node_id: NodeId, index: usize) -> Option<Entry<P, V, N>> {
        let left_id = self.node(node_id).children[index];
        let right_id = self.node(node_id).children[index + 1];

        if self.node(left_id).entries.len() >= T {
            let predecessor = self.remove_max_entry(left_id);
            let old = mem::replace(&mut self.node_mut(node_id).entries[index], predecessor);
            self.pull(node_id);
            return Some(old);
        }

        if self.node(right_id).entries.len() >= T {
            let successor = self.remove_min_entry(right_id);
            let old = mem::replace(&mut self.node_mut(node_id).entries[index], successor);
            self.pull(node_id);
            return Some(old);
        }

        let target_key = self.node(node_id).entries[index].key.clone();
        let merged_id = self.merge_children_around_entry(node_id, index);
        let removed = self.delete_from_node(merged_id, &target_key);
        self.pull(node_id);
        removed
    }

    fn remove_min_entry(&mut self, node_id: NodeId) -> Entry<P, V, N> {
        if self.node(node_id).leaf {
            let entry = self.node_mut(node_id).entries.remove(0);
            self.pull(node_id);
            return entry;
        }
        let child_index = self.ensure_child_has_at_least_t(node_id, 0);
        debug_assert_eq!(child_index, 0);
        let child_id = self.node(node_id).children[child_index];
        let entry = self.remove_min_entry(child_id);
        self.pull(node_id);
        entry
    }

    fn remove_max_entry(&mut self, node_id: NodeId) -> Entry<P, V, N> {
        if self.node(node_id).leaf {
            let entry = self
                .node_mut(node_id)
                .entries
                .pop()
                .expect("remove_max_entry on empty node");
            self.pull(node_id);
            return entry;
        }
        let last_child_index = self.node(node_id).children.len() - 1;
        // If the rightmost child gets merged into its left sibling, the
        // returned index is last_child_index - 1; always use the return value.
        let child_index = self.ensure_child_has_at_least_t(node_id, last_child_index);
        let child_id = self.node(node_id).children[child_index];
        let entry = self.remove_max_entry(child_id);
        self.pull(node_id);
        entry
    }

    /// Ensures `parent.children[index]` has at least `T` entries before a
    /// descent, borrowing from a sibling or merging. Returns the (possibly
    /// shifted) index of the child to descend into.
    fn ensure_child_has_at_least_t(&mut self, parent_id: NodeId, index: usize) -> usize {
        let child_id = self.node(parent_id).children[index];
        if self.node(child_id).entries.len() >= T {
            return index;
        }

        if index > 0 {
            let left_id = self.node(parent_id).children[index - 1];
            if self.node(left_id).entries.len() >= T {
                self.borrow_from_left(parent_id, index);
                return index;
            }
        }

        if index + 1 < self.node(parent_id).children.len() {
            let right_id = self.node(parent_id).children[index + 1];
            if self.node(right_id).entries.len() >= T {
                self.borrow_from_right(parent_id, index);
                return index;
            }
        }

        if index > 0 {
            self.merge_children_around_entry(parent_id, index - 1);
            index - 1
        } else {
            self.merge_children_around_entry(parent_id, index);
            index
        }
    }

    /// Rotates the separator down into `children[index]` and the left
    /// sibling's max entry up into the parent.
    fn borrow_from_left(&mut self, parent_id: NodeId, index: usize) {
        let left_id = self.node(parent_id).children[index - 1];
        let child_id = self.node(parent_id).children[index];

        let up_entry = self
            .node_mut(left_id)
            .entries
            .pop()
            .expect("borrow_from_left from empty sibling");
        let down_entry = mem::replace(&mut self.node_mut(parent_id).entries[index - 1], up_entry);
        self.node_mut(child_id).entries.insert(0, down_entry);

        if !self.node(child_id).leaf {
            let moved_child = self
                .node_mut(left_id)
                .children
                .pop()
                .expect("internal sibling has children");
            self.node_mut(child_id).children.insert(0, moved_child);
        }

        self.pull(left_id);
        self.pull(child_id);
        self.pull(parent_id);
    }

    /// Rotates the separator down into `children[index]` and the right
    /// sibling's min entry up into the parent.
    fn borrow_from_right(&mut self, parent_id: NodeId, index: usize) {
        let child_id = self.node(parent_id).children[index];
        let right_id = self.node(parent_id).children[index + 1];

        let up_entry = self.node_mut(right_id).entries.remove(0);
        let down_entry = mem::replace(&mut self.node_mut(parent_id).entries[index], up_entry);
        self.node_mut(child_id).entries.push(down_entry);

        if !self.node(child_id).leaf {
            let moved_child = self.node_mut(right_id).children.remove(0);
            self.node_mut(child_id).children.push(moved_child);
        }

        self.pull(child_id);
        self.pull(right_id);
        self.pull(parent_id);
    }

    /// Merges `children[index]`, `entries[index]`, and `children[index + 1]`
    /// into the left child. Frees the right child and returns the merged id.
    fn merge_children_around_entry(&mut self, parent_id: NodeId, index: usize) -> NodeId {
        let left_id = self.node(parent_id).children[index];
        let right_id = self.node(parent_id).children[index + 1];

        let separator = self.node_mut(parent_id).entries.remove(index);
        self.node_mut(parent_id).children.remove(index + 1);

        let right = self.nodes[right_id.0].take().expect("dangling NodeId");
        self.free_list.push(right_id);

        let left = self.node_mut(left_id);
        left.entries.push(separator);
        left.entries.extend(right.entries);
        left.children.extend(right.children);

        self.pull(left_id);
        self.pull(parent_id);
        left_id
    }
}

#[cfg(test)]
impl<P: Ord + Clone, V, const T: usize, const N: usize> AffinityBTreeQueue<P, V, T, N> {
    pub(crate) fn debug_set_next_seq(&mut self, seq: Seq) {
        self.next_seq = seq;
    }

    fn for_each_entry_in_order<F: FnMut(&Entry<P, V, N>)>(&self, mut f: F) {
        enum Item {
            Visit(NodeId),
            Emit(NodeId, usize),
        }

        let Some(root) = self.root else { return };
        let mut stack = Vec::new();
        stack.push(Item::Visit(root));

        while let Some(item) = stack.pop() {
            match item {
                Item::Visit(id) => {
                    let x = self.node(id);
                    if x.leaf {
                        for e in &x.entries {
                            f(e);
                        }
                    } else {
                        let n = x.entries.len();
                        // Push in reverse so child[0] is processed first:
                        // child[0], entry[0], child[1], ..., entry[n-1], child[n].
                        stack.push(Item::Visit(x.children[n]));
                        let mut i = n;
                        while i > 0 {
                            i -= 1;
                            stack.push(Item::Emit(id, i));
                            stack.push(Item::Visit(x.children[i]));
                        }
                    }
                }
                Item::Emit(id, i) => f(&self.node(id).entries[i]),
            }
        }
    }

    pub(crate) fn debug_count_entries(&self) -> usize {
        let mut count = 0;
        self.for_each_entry_in_order(|_| count += 1);
        count
    }

    pub(crate) fn debug_all_keys_in_order(&self) -> Vec<PriorityKey<P>> {
        let mut out = Vec::new();
        self.for_each_entry_in_order(|e| out.push(e.key.clone()));
        out
    }

    /// Asserts every structural, key-order, augmentation, and arena invariant.
    pub(crate) fn check_invariants(&self) {
        for id in &self.free_list {
            assert!(
                self.nodes[id.0].is_none(),
                "free_list entry points to a live node"
            );
        }

        let Some(root) = self.root else {
            assert_eq!(self.len, 0, "empty tree must have len 0");
            assert!(
                self.nodes.iter().all(|n| n.is_none()),
                "empty tree must have no live nodes"
            );
            assert_eq!(self.free_list.len(), self.nodes.len());
            return;
        };
        assert!(self.len > 0, "non-empty root with len 0");

        struct WorkItem<P> {
            id: NodeId,
            is_root: bool,
            min_key: Option<PriorityKey<P>>,
            max_key: Option<PriorityKey<P>>,
            depth: usize,
        }

        let mut total_entries = 0usize;
        let mut total_nodes = 0usize;
        let mut leaf_depth: Option<usize> = None;

        let mut stack: Vec<WorkItem<P>> = Vec::new();
        stack.push(WorkItem {
            id: root,
            is_root: true,
            min_key: None,
            max_key: None,
            depth: 0,
        });

        while let Some(item) = stack.pop() {
            let x = self.node(item.id);
            total_nodes += 1;
            total_entries += x.entries.len();

            assert!(x.entries.len() <= Self::MAX_KEYS, "node overflow");
            if item.is_root {
                assert!(!x.entries.is_empty(), "root must be non-empty");
            } else {
                assert!(x.entries.len() >= Self::MIN_KEYS, "non-root underflow");
            }

            for w in x.entries.windows(2) {
                assert!(w[0].key < w[1].key, "node entries not strictly sorted");
            }
            for e in &x.entries {
                if let Some(m) = &item.min_key {
                    assert!(*m < e.key, "entry below child key range");
                }
                if let Some(m) = &item.max_key {
                    assert!(e.key < *m, "entry above child key range");
                }
                assert!(!e.affinity.is_empty(), "entry with empty affinity");
                assert!(
                    e.affinity.fits_within(self.num_cpus),
                    "entry affinity outside num_cpus"
                );
            }

            let mut mask = CpuMask::empty();
            for e in &x.entries {
                mask = mask.union(e.affinity);
            }

            if x.leaf {
                assert!(x.children.is_empty(), "leaf with children");
                match leaf_depth {
                    None => leaf_depth = Some(item.depth),
                    Some(d) => assert_eq!(d, item.depth, "leaves at different depths"),
                }
            } else {
                assert_eq!(
                    x.children.len(),
                    x.entries.len() + 1,
                    "internal node child count"
                );
                for ci in 0..x.children.len() {
                    let child_id = x.children[ci];
                    mask = mask.union(self.node(child_id).subtree_affinity);
                    stack.push(WorkItem {
                        id: child_id,
                        is_root: false,
                        min_key: if ci == 0 {
                            item.min_key.clone()
                        } else {
                            Some(x.entries[ci - 1].key.clone())
                        },
                        max_key: if ci == x.entries.len() {
                            item.max_key.clone()
                        } else {
                            Some(x.entries[ci].key.clone())
                        },
                        depth: item.depth + 1,
                    });
                }
            }

            assert_eq!(mask, x.subtree_affinity, "stale subtree_affinity");
        }

        assert_eq!(total_entries, self.len, "entry count != len");
        let live = self.nodes.iter().filter(|n| n.is_some()).count();
        assert_eq!(live, total_nodes, "unreachable live nodes in arena");
        assert_eq!(live + self.free_list.len(), self.nodes.len());

        {
            let keys = self.debug_all_keys_in_order();
            for w in keys.windows(2) {
                assert!(w[0] < w[1], "in-order keys not strictly sorted");
            }
        }
    }
}

#[cfg(test)]
impl<P: Ord + Clone, V: Clone, const T: usize, const N: usize> AffinityBTreeQueue<P, V, T, N> {
    pub(crate) fn debug_all_entries_in_order(&self) -> Vec<(PriorityKey<P>, CpuMask<N>, V)> {
        let mut out = Vec::new();
        self.for_each_entry_in_order(|e| out.push((e.key.clone(), e.affinity, e.value.clone())));
        out
    }
}

/// Deliberately simple Vec-based reference model used by tests to check the
/// B-tree's observable behavior.
#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
struct RefEntry<P, V, const N: usize> {
    key: PriorityKey<P>,
    affinity: CpuMask<N>,
    value: V,
}

#[cfg(test)]
#[derive(Clone, Debug)]
struct RefModel<P, V, const N: usize = 1> {
    entries: Vec<RefEntry<P, V, N>>,
    next_seq: Seq,
    num_cpus: usize,
}

#[cfg(test)]
impl<P: Ord + Clone, V: Clone, const N: usize> RefModel<P, V, N> {
    fn new(num_cpus: usize) -> Self {
        Self {
            entries: Vec::new(),
            next_seq: 0,
            num_cpus,
        }
    }

    fn push(
        &mut self,
        priority: P,
        affinity: CpuMask<N>,
        value: V,
    ) -> Result<PriorityKey<P>, PushError> {
        if affinity.is_empty() {
            return Err(PushError::EmptyAffinity);
        }
        if !affinity.fits_within(self.num_cpus) {
            return Err(PushError::InvalidCpu);
        }
        let seq = self.next_seq;
        let next_seq = seq.checked_add(1).ok_or(PushError::SequenceOverflow)?;
        self.next_seq = next_seq;

        let key = PriorityKey { priority, seq };
        self.entries.push(RefEntry {
            key: key.clone(),
            affinity,
            value,
        });
        Ok(key)
    }

    fn peek_key_for_cpu(&self, cpu: usize) -> Option<PriorityKey<P>> {
        if cpu >= self.num_cpus {
            return None;
        }
        self.entries
            .iter()
            .filter(|e| e.affinity.contains(cpu))
            .map(|e| e.key.clone())
            .min()
    }

    fn pop_for_cpu(&mut self, cpu: usize) -> Option<(PriorityKey<P>, CpuMask<N>, V)> {
        let key = self.peek_key_for_cpu(cpu)?;
        let index = self.entries.iter().position(|e| e.key == key).unwrap();
        let entry = self.entries.remove(index);
        Some((entry.key, entry.affinity, entry.value))
    }

    fn remove(&mut self, key: &PriorityKey<P>) -> Option<(PriorityKey<P>, CpuMask<N>, V)> {
        let index = self.entries.iter().position(|e| e.key == *key)?;
        let entry = self.entries.remove(index);
        Some((entry.key, entry.affinity, entry.value))
    }

    fn len(&self) -> usize {
        self.entries.len()
    }

    fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn entries_in_order(&self) -> Vec<(PriorityKey<P>, CpuMask<N>, V)> {
        let mut out: Vec<_> = self
            .entries
            .iter()
            .map(|e| (e.key.clone(), e.affinity, e.value.clone()))
            .collect();
        out.sort_by(|a, b| a.0.cmp(&b.0));
        out
    }
}

#[cfg(test)]
mod tests;
