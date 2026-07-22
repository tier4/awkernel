# Affinity BTree Queue

An affinity-aware priority queue backed by an augmented classical (CLRS-style) B-tree, written in Rust.

Each entry carries `(priority, affinity: CpuMask, value)`.
`pop_for_cpu(cpu)` returns the highest-priority entry whose affinity includes that CPU in O(log N),
making it suitable for task schedulers where tasks are pinned to specific CPUs.

## Features

- **Affinity-aware scheduling** — every node stores the OR of all affinities in its subtree;
  `pop_for_cpu` prunes ineligible subtrees in a single traversal
- **`no_std` + `alloc`** — works in embedded and OS-kernel environments
- **O(log N)** push / pop / remove via an arena-based augmented B-tree
- **Generic priority** — any `P: Ord`; smaller value = higher priority;
  use `core::cmp::Reverse` for max-first order
- **Configurable CPU count** — `CpuMask<N>` supports up to `N × 64` CPUs
  (default `N = 1` → 64 CPUs, `N = 2` → 128 CPUs, …)
- **No unsafe code** — `#![forbid(unsafe_code)]`

## Usage

Add the crate to `Cargo.toml`:

```toml
[dependencies]
affinity_btree_queue = { path = "..." }
```

### Basic example

```rust
use affinity_btree_queue::{AffinityBTreeQueue, CpuMask};

// Create a queue for a 4-CPU system.
// Smaller priority value = higher priority.
let mut q: AffinityBTreeQueue<u32, &str> = AffinityBTreeQueue::new(4);

// Build CPU affinity masks.
let mut cpu0 = CpuMask::empty();
cpu0.insert(0);

let mut cpu12 = CpuMask::empty();
cpu12.insert(1);
cpu12.insert(2);

let mut all = CpuMask::empty();
for c in 0..4 { all.insert(c); }

// push returns a PriorityKey handle that can be passed to remove() later.
q.push(10, all,   "low priority, any CPU").unwrap();
q.push(5,  cpu12, "medium, CPUs 1-2 only").unwrap();
q.push(1,  cpu0,  "high priority, CPU 0 only").unwrap();

// pop_for_cpu returns the highest-priority entry runnable on the given CPU.
let (_, _, v) = q.pop_for_cpu(0).unwrap();
assert_eq!(v, "high priority, CPU 0 only"); // priority=1

// The cpu12 entry (priority=5) is not runnable on CPU 0, so priority=10 is next.
let (_, _, v) = q.pop_for_cpu(0).unwrap();
assert_eq!(v, "low priority, any CPU");     // priority=10

// CPU 1 can run the cpu12 entry (priority=5).
let (_, _, v) = q.pop_for_cpu(1).unwrap();
assert_eq!(v, "medium, CPUs 1-2 only");     // priority=5
```

### Max-first ordering with `Reverse`

```rust
use affinity_btree_queue::{AffinityBTreeQueue, CpuMask};
use core::cmp::Reverse;

let mut q: AffinityBTreeQueue<Reverse<u32>, u32> = AffinityBTreeQueue::new(1);
let mut m = CpuMask::empty();
m.insert(0);
q.push(Reverse(1),   m, 1).unwrap();
q.push(Reverse(100), m, 100).unwrap();

// Reverse(100) < Reverse(1), so the numerically larger value dequeues first.
let (_, _, v) = q.pop_for_cpu(0).unwrap();
assert_eq!(v, 100);
```

## API overview

### `AffinityBTreeQueue<P, V, const T = 16, const N = 1>`

| Method | Description |
|--------|-------------|
| `new(num_cpus)` | Create an empty queue for CPUs `0..num_cpus` |
| `push(priority, affinity, value)` | Insert an entry; returns a `PriorityKey` handle |
| `pop_for_cpu(cpu)` | Remove and return the highest-priority entry runnable on `cpu` |
| `peek_key_for_cpu(cpu)` | Return the key of the best entry for `cpu` without removing it |
| `remove(&key)` | Remove an entry by its `PriorityKey` |
| `len()` / `is_empty()` | Entry count |
| `num_cpus()` | Configured CPU count |

Type parameters: `P: Ord` (priority), `V` (value), `T` (B-tree minimum degree, default 16),
`N` (words in `CpuMask`, default 1).

### `CpuMask<const N = 1>`

| Method | Description |
|--------|-------------|
| `empty()` | All-zero mask |
| `insert(cpu)` | Set the bit for `cpu` |
| `contains(cpu)` | Test whether `cpu` is set |
| `union(other)` | Bitwise OR of two masks |
| `from_bits_truncate(bits)` | Construct from a raw `u64` (word 0) |

### `PushError`

| Variant | Meaning |
|---------|---------|
| `EmptyAffinity` | `affinity` has no bits set |
| `InvalidCpu` | `affinity` has a bit set for a CPU ≥ `num_cpus` |
| `SequenceOverflow` | Internal sequence counter exhausted (2⁶⁴ pushes) |

## Building and testing

```bash
cargo build
cargo test        # unit tests + randomized property tests + doctests
```

Tests compare every operation against a simple `Vec`-based reference model and verify
all B-tree structural invariants (key order, subtree affinity summaries, leaf depth
uniformity, entry count) after every mutation.

## Implementation notes

- The tree is an **arena-based augmented B-tree** (`Vec<Option<Node>>` + free list).
  Node IDs are stable indices; the arena is never compacted.
- Every node stores **`subtree_affinity`** = OR of all entry affinities in its subtree.
  `pop_for_cpu` uses this summary to skip entire subtrees with no eligible entry.
- Ordering is by **`(priority, seq)`** — the monotonically increasing `seq` counter
  makes every key unique, so no two entries ever compare equal.
- Priority / affinity updates are **remove + re-insert**; no in-place mutation of keys.
- Deletion is **top-down**: before descending into a child, the algorithm ensures it has
  ≥ T entries (borrowing from a sibling or merging), so underflow never propagates upward.

## License

This project is licensed under either of

- Apache License, Version 2.0
- MIT license

at your option.

## Test Coverage

[coverage.txt](coverage.txt) contains line-by-line coverage data from `cargo llvm-cov` for the latest test run.

```bash
cargo llvm-cov --workspace --all-features --text --output-path coverage.txt
cargo llvm-cov --workspace --all-features --lcov --output-path lcov.info
```
