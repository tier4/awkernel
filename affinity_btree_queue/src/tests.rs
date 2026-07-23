use super::*;
use alloc::vec::Vec;
use core::cmp::Reverse;

/// Degree-2 queue: every structural case (split, borrow, merge, root shrink)
/// is reachable with a handful of entries.
type Q2 = AffinityBTreeQueue<u32, u32, 2>;
/// Production-degree queue.
type Q16 = AffinityBTreeQueue<u32, u32>;

fn mask(cpus: &[usize]) -> CpuMask {
    let mut m = CpuMask::empty();
    for &c in cpus {
        m.insert(c);
    }
    m
}

fn all_cpus<const N: usize>(num_cpus: usize) -> CpuMask<N> {
    let mut m = CpuMask::empty();
    for cpu in 0..num_cpus {
        m.insert(cpu);
    }
    m
}

struct XorShift64 {
    state: u64,
}

impl XorShift64 {
    fn new(seed: u64) -> Self {
        Self {
            state: seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).max(1),
        }
    }

    fn next(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }
}

// ---------------------------------------------------------------------------
// CpuMask
// ---------------------------------------------------------------------------

#[test]
fn cpu_mask_basics() {
    let mut m = CpuMask::empty();
    assert!(m.is_empty());
    assert!(!m.contains(0));
    m.insert(0);
    m.insert(63);
    assert!(m.contains(0));
    assert!(m.contains(63));
    assert!(!m.contains(1));
    assert!(!m.contains(64));
    assert!(!m.contains(1000));
    assert_eq!(m.union(mask(&[1])), mask(&[0, 1, 63]));
    assert!(mask(&[3]).fits_within(4));
    assert!(!mask(&[4]).fits_within(4));
    assert!(mask(&[63]).fits_within(64));
}

#[test]
fn cpu_mask_wide() {
    let mut m = CpuMask::<2>::empty();
    assert!(m.is_empty());
    m.insert(0);
    m.insert(63);
    m.insert(64);
    m.insert(127);
    assert!(m.contains(0));
    assert!(m.contains(63));
    assert!(m.contains(64));
    assert!(m.contains(127));
    assert!(!m.contains(1));
    assert!(!m.contains(128));
    assert!(!m.contains(10000));

    assert!(m.fits_within(128));
    assert!(!m.fits_within(127)); // bit 127 is set
    assert!(!m.fits_within(64)); // bits 64+ are set
    assert!(!m.fits_within(63)); // bits 63+ are set

    let mut a = CpuMask::<2>::empty();
    a.insert(65);
    let mut b = CpuMask::<2>::empty();
    b.insert(70);
    let c = a.union(b);
    assert!(c.contains(65));
    assert!(c.contains(70));
    assert!(!c.contains(66));

    let mut w = CpuMask::<2>::empty();
    w.set_word(0, 0xAB);
    w.set_word(1, 0xCD);
    assert_eq!(w.word(0), 0xAB);
    assert_eq!(w.word(1), 0xCD);
}

#[test]
fn cpu_mask_from_bits_truncate_and_bits() {
    let m: CpuMask = CpuMask::from_bits_truncate(0b0101);
    assert!(m.contains(0));
    assert!(!m.contains(1));
    assert!(m.contains(2));
    assert_eq!(m.bits(), 0b0101);

    let zero: CpuMask = CpuMask::from_bits_truncate(0);
    assert!(zero.is_empty());
    assert_eq!(zero.bits(), 0);
}

#[test]
fn cpu_mask_const_builders() {
    // All constructors must be usable in const contexts.
    const M: CpuMask<2> = CpuMask::empty().with(1).with(64).without(1);
    assert!(!M.contains(1));
    assert!(M.contains(64));

    const ALL: CpuMask<2> = CpuMask::all();
    assert!(ALL.contains(0));
    assert!(ALL.contains(127));

    const WORKERS: CpuMask<2> = CpuMask::all().masked_below(4).without(0);
    assert_eq!(WORKERS, CpuMask::empty().with(1).with(2).with(3));
}

#[test]
fn cpu_mask_remove() {
    let mut m = CpuMask::<2>::empty();
    m.insert(0);
    m.insert(64);
    m.remove(0);
    assert!(!m.contains(0));
    assert!(m.contains(64));
    m.remove(64);
    assert!(m.is_empty());
    // Removing an already-clear bit is a no-op.
    m.remove(1);
    assert!(m.is_empty());
}

#[test]
fn cpu_mask_masked_below_word_boundaries() {
    let all = CpuMask::<2>::all();

    assert!(all.masked_below(0).is_empty());

    assert_eq!(all.masked_below(1), CpuMask::empty().with(0));

    let below63 = all.masked_below(63);
    assert!(below63.contains(62));
    assert!(!below63.contains(63));

    let below64 = all.masked_below(64);
    assert_eq!(below64.word(0), u64::MAX);
    assert_eq!(below64.word(1), 0);

    let below65 = all.masked_below(65);
    assert_eq!(below65.word(0), u64::MAX);
    assert_eq!(below65.word(1), 1);

    // n >= N * 64 keeps every bit.
    assert_eq!(all.masked_below(128), all);
    assert_eq!(all.masked_below(1000), all);

    // Already-clear bits stay clear.
    let sparse = CpuMask::<2>::empty().with(1).with(70);
    assert_eq!(sparse.masked_below(70), CpuMask::empty().with(1));
}

#[test]
fn cpu_mask_iter() {
    // Empty mask yields nothing.
    assert_eq!(CpuMask::<2>::empty().iter().count(), 0);

    // Ascending order across word boundaries; zero words are skipped.
    let m = CpuMask::<2>::empty().with(1).with(63).with(64).with(127);
    let cpus: Vec<usize> = m.iter().collect();
    assert_eq!(cpus, [1, 63, 64, 127]);

    // A mask whose first word is zero.
    let hi = CpuMask::<2>::empty().with(100);
    assert_eq!(hi.iter().collect::<Vec<_>>(), [100]);

    // Full mask yields every index.
    let all: Vec<usize> = CpuMask::<2>::all().iter().collect();
    assert_eq!(all.len(), 128);
    assert_eq!(all[0], 0);
    assert_eq!(all[127], 127);
}

#[test]
fn fits_within_upper_word_all_zero() {
    // word 0 has bits; word 1 is entirely zero.
    // fits_within(64): full_words=1, extra_bits=0, upper_start=1
    // Loop for i in 1..2: self.0[1]==0 → no early return, falls through line 199.
    let mut m = CpuMask::<2>::empty();
    m.insert(0);
    m.insert(63);
    assert!(m.fits_within(64));
}

#[test]
fn priority_key_ordering() {
    let a = PriorityKey {
        priority: 1u32,
        seq: 5,
    };
    let b = PriorityKey {
        priority: 2u32,
        seq: 0,
    };
    let c = PriorityKey {
        priority: 1u32,
        seq: 6,
    };
    assert!(a < b);
    assert!(a < c);
    assert!(c < b);
    assert_eq!(a, a.clone());
}

// ---------------------------------------------------------------------------
// Basic operations
// ---------------------------------------------------------------------------

#[test]
fn queue_num_cpus_getter() {
    let q: Q16 = AffinityBTreeQueue::new(8);
    assert_eq!(q.num_cpus(), 8);
    let q2: Q2 = AffinityBTreeQueue::new(2);
    assert_eq!(q2.num_cpus(), 2);
}

#[test]
fn queue_affinity_mask_tracks_entries() {
    let mut q = Q16::new(4);
    assert!(q.affinity_mask().is_empty());

    let k1 = q.push(10, mask(&[1]), 100).unwrap();
    assert_eq!(q.affinity_mask(), mask(&[1]));

    q.push(20, mask(&[2, 3]), 200).unwrap();
    assert_eq!(q.affinity_mask(), mask(&[1, 2, 3]));

    // Two entries share CPU 1; removing one must keep the bit set.
    q.push(30, mask(&[1]), 300).unwrap();
    q.remove(&k1).unwrap();
    assert_eq!(q.affinity_mask(), mask(&[1, 2, 3]));

    assert!(q.pop_for_cpu(1).is_some());
    assert_eq!(q.affinity_mask(), mask(&[2, 3]));

    assert!(q.pop_for_cpu(3).is_some());
    assert!(q.affinity_mask().is_empty());
    q.check_invariants();
}

#[test]
fn queue_affinity_mask_with_deep_tree() {
    // Force splits (T=2) so the mask is aggregated across multiple levels.
    let mut q = Q2::new(2);
    for i in 0..64u32 {
        let cpu = (i % 2) as usize;
        q.push(i, mask(&[cpu]), i).unwrap();
    }
    assert_eq!(q.affinity_mask(), mask(&[0, 1]));

    // Drain every CPU-0 entry; only CPU-1 entries remain.
    while q.pop_for_cpu(0).is_some() {}
    assert_eq!(q.affinity_mask(), mask(&[1]));

    while q.pop_for_cpu(1).is_some() {}
    assert!(q.affinity_mask().is_empty());
    q.check_invariants();
}

#[test]
fn empty_tree_pop_for_cpu() {
    let mut q = Q16::new(4);
    assert_eq!(q.len(), 0);
    assert!(q.is_empty());
    for cpu in 0..4 {
        assert_eq!(q.peek_key_for_cpu(cpu), None);
        assert_eq!(q.pop_for_cpu(cpu), None);
    }
    assert_eq!(q.pop_for_cpu(99), None);
    q.check_invariants();
}

#[test]
fn single_insert_and_pop() {
    let mut q = Q16::new(4);
    let key = q.push(10, mask(&[1, 2]), 100).unwrap();
    q.check_invariants();
    assert_eq!(q.len(), 1);
    assert_eq!(q.peek_key_for_cpu(0), None);
    assert_eq!(q.peek_key_for_cpu(1), Some(key.clone()));
    assert_eq!(q.pop_for_cpu(2), Some((key, mask(&[1, 2]), 100)));
    assert!(q.is_empty());
    q.check_invariants();
}

#[test]
fn single_insert_and_remove() {
    let mut q = Q16::new(4);
    let key = q.push(10, mask(&[0]), 7).unwrap();
    assert_eq!(q.remove(&key), Some((key.clone(), mask(&[0]), 7)));
    assert_eq!(q.remove(&key), None);
    assert!(q.is_empty());
    q.check_invariants();
}

#[test]
fn same_priority_multiple_sequence_numbers() {
    let mut q = Q2::new(2);
    let mut keys = Vec::new();
    for i in 0..8u32 {
        let key = q.push(7, mask(&[0]), i).unwrap();
        keys.push(key);
        q.check_invariants();
    }
    // All same priority: dequeue order must follow seq (FIFO).
    for (i, expected) in keys.into_iter().enumerate() {
        let (key, _, value) = q.pop_for_cpu(0).unwrap();
        assert_eq!(key, expected);
        assert_eq!(value, i as u32);
        q.check_invariants();
    }
    assert!(q.is_empty());
}

#[test]
fn sequence_number_uniqueness() {
    let mut q = Q16::new(1);
    let mut seqs = Vec::new();
    for _ in 0..50 {
        let key = q.push(3, mask(&[0]), 0).unwrap();
        assert!(!seqs.contains(&key.seq));
        seqs.push(key.seq);
    }
    for w in seqs.windows(2) {
        assert!(w[0] < w[1]);
    }
}

#[test]
fn ascending_priority_insertion() {
    let mut q = Q16::new(4);
    for p in 0..300u32 {
        q.push(p, all_cpus(4), p).unwrap();
        q.check_invariants();
    }
    for p in 0..300u32 {
        let (key, _, value) = q.pop_for_cpu((p as usize) % 4).unwrap();
        assert_eq!(key.priority, p);
        assert_eq!(value, p);
        q.check_invariants();
    }
    assert!(q.is_empty());
}

#[test]
fn descending_priority_insertion() {
    let mut q = Q16::new(4);
    for p in (0..300u32).rev() {
        q.push(p, all_cpus(4), p).unwrap();
        q.check_invariants();
    }
    for p in 0..300u32 {
        let (key, _, value) = q.pop_for_cpu(0).unwrap();
        assert_eq!(key.priority, p);
        assert_eq!(value, p);
        q.check_invariants();
    }
}

#[test]
fn random_priority_insertion() {
    let mut rng = XorShift64::new(42);
    let mut q = Q16::new(4);
    let mut model = RefModel::<u32, u32>::new(4);
    for i in 0..500u32 {
        let p = (rng.next() % 100) as u32;
        assert_eq!(q.push(p, all_cpus(4), i), model.push(p, all_cpus(4), i));
        q.check_invariants();
    }
    while !model.is_empty() {
        assert_eq!(q.pop_for_cpu(1), model.pop_for_cpu(1));
        q.check_invariants();
    }
    assert!(q.is_empty());
}

// ---------------------------------------------------------------------------
// Structural cases (degree 2 makes shapes deterministic)
// ---------------------------------------------------------------------------

/// Pushes priorities 10, 20, 30, 40 into a T=2 queue, producing the shape
/// root=[20], left=[10], right=[30,40]. Returns the key of priority 20.
fn build_split_tree(q: &mut Q2) -> PriorityKey<u32> {
    let mut key20 = None;
    for p in [10u32, 20, 30, 40] {
        let key = q.push(p, mask(&[0]), p).unwrap();
        if p == 20 {
            key20 = Some(key);
        }
        q.check_invariants();
    }
    key20.unwrap()
}

fn pop_all_priorities(q: &mut Q2, cpu: usize) -> Vec<u32> {
    let mut out = Vec::new();
    while let Some((key, _, _)) = q.pop_for_cpu(cpu) {
        out.push(key.priority);
        q.check_invariants();
    }
    out
}

#[test]
fn root_split() {
    let mut q = Q2::new(1);
    build_split_tree(&mut q);
    assert_eq!(q.len(), 4);
    assert_eq!(pop_all_priorities(&mut q, 0), [10, 20, 30, 40]);
}

#[test]
fn multiple_level_split() {
    let mut q = Q2::new(2);
    for p in 0..60u32 {
        q.push(p, mask(&[(p % 2) as usize]), p).unwrap();
        q.check_invariants();
    }
    assert_eq!(q.len(), 60);
    let evens = pop_all_priorities(&mut q, 0);
    assert_eq!(evens, (0..60).filter(|p| p % 2 == 0).collect::<Vec<_>>());
    q.check_invariants();

    let odds = pop_all_priorities(&mut q, 1);
    assert_eq!(odds, (0..60).filter(|p| p % 2 == 1).collect::<Vec<_>>());
    assert!(q.is_empty());
}

#[test]
fn multiple_level_split_production_degree() {
    let mut q = Q16::new(4);
    // > MAX_KEYS + (MAX_KEYS + 1) * MAX_KEYS = 1023 entries forces height >= 3.
    for p in 0..1200u32 {
        q.push(p, all_cpus(4), p).unwrap();
        if p % 50 == 0 {
            q.check_invariants();
        }
    }
    q.check_invariants();
    assert_eq!(q.len(), 1200);
    for p in 0..1200u32 {
        let (key, _, _) = q.pop_for_cpu(3).unwrap();
        assert_eq!(key.priority, p);
        if p % 50 == 0 {
            q.check_invariants();
        }
    }
    q.check_invariants();
}

#[test]
fn root_shrink_after_deletion() {
    let mut q = Q2::new(1);
    let mut keys = Vec::new();
    for p in 0..20u32 {
        keys.push(q.push(p, mask(&[0]), p).unwrap());
    }
    q.check_invariants();
    for key in keys {
        assert!(q.remove(&key).is_some());
        q.check_invariants();
    }
    assert!(q.is_empty());
    assert_eq!(q.peek_key_for_cpu(0), None);
}

#[test]
fn delete_from_leaf() {
    let mut q = Q2::new(1);
    let k10 = q.push(10, mask(&[0]), 10).unwrap();
    let k20 = q.push(20, mask(&[0]), 20).unwrap();
    let k30 = q.push(30, mask(&[0]), 30).unwrap();
    // Root is still a single leaf [10, 20, 30].
    assert_eq!(q.remove(&k20), Some((k20, mask(&[0]), 20)));
    q.check_invariants();
    assert_eq!(q.remove(&k10), Some((k10, mask(&[0]), 10)));
    q.check_invariants();
    assert_eq!(q.remove(&k30), Some((k30, mask(&[0]), 30)));
    q.check_invariants();
    assert!(q.is_empty());
}

#[test]
fn delete_internal_entry_using_predecessor() {
    let mut q = Q2::new(1);
    let key20 = build_split_tree(&mut q);
    // Push 5 so the left child [5,10] has T=2 entries: removing the internal
    // key 20 must take the predecessor (10) from the left child.
    q.push(5, mask(&[0]), 5).unwrap();
    q.check_invariants();
    assert!(q.remove(&key20).is_some());
    q.check_invariants();
    assert_eq!(pop_all_priorities(&mut q, 0), [5, 10, 30, 40]);
}

#[test]
fn delete_internal_entry_using_successor() {
    let mut q = Q2::new(1);
    let key20 = build_split_tree(&mut q);
    // Shape: root=[20], left=[10], right=[30,40]. Left child is minimal but
    // the right child has T entries: must take the successor (30).
    assert!(q.remove(&key20).is_some());
    q.check_invariants();
    assert_eq!(pop_all_priorities(&mut q, 0), [10, 30, 40]);
}

#[test]
fn delete_internal_entry_using_merge() {
    let mut q = Q2::new(1);
    let key20 = build_split_tree(&mut q);
    // Trim the right child to [30] so both children are minimal: removing the
    // internal key 20 must merge left + separator + right, then root-shrink.
    let (k40, _, _) = {
        let mut found = None;
        let keys = q.debug_all_keys_in_order();
        for key in keys {
            if key.priority == 40 {
                found = Some(key);
            }
        }
        (found.unwrap(), (), ())
    };
    assert!(q.remove(&k40).is_some());
    q.check_invariants();
    assert!(q.remove(&key20).is_some());
    q.check_invariants();
    assert_eq!(pop_all_priorities(&mut q, 0), [10, 30]);
}

#[test]
fn borrow_from_left_sibling() {
    let mut q = Q2::new(1);
    build_split_tree(&mut q);
    q.push(5, mask(&[0]), 5).unwrap();
    // Shape: root=[20], left=[5,10], right=[30,40]. Trim right to [30].
    let k40 = q
        .debug_all_keys_in_order()
        .into_iter()
        .find(|k| k.priority == 40)
        .unwrap();
    assert!(q.remove(&k40).is_some());
    q.check_invariants();
    // Removing 30 descends into the minimal right child; the left sibling has
    // T entries, so the fix-up must borrow from the left.
    let k30 = q
        .debug_all_keys_in_order()
        .into_iter()
        .find(|k| k.priority == 30)
        .unwrap();
    assert!(q.remove(&k30).is_some());
    q.check_invariants();
    assert_eq!(pop_all_priorities(&mut q, 0), [5, 10, 20]);
}

#[test]
fn borrow_from_right_sibling() {
    let mut q = Q2::new(1);
    build_split_tree(&mut q);
    // Shape: root=[20], left=[10], right=[30,40]. Removing 10 descends into
    // the minimal left child; the right sibling has T entries, so the fix-up
    // must borrow from the right.
    let k10 = q
        .debug_all_keys_in_order()
        .into_iter()
        .find(|k| k.priority == 10)
        .unwrap();
    assert!(q.remove(&k10).is_some());
    q.check_invariants();
    assert_eq!(pop_all_priorities(&mut q, 0), [20, 30, 40]);
}

#[test]
fn merge_children() {
    let mut q = Q2::new(1);
    build_split_tree(&mut q);
    // Trim right child to [30]: both children minimal.
    let k40 = q
        .debug_all_keys_in_order()
        .into_iter()
        .find(|k| k.priority == 40)
        .unwrap();
    assert!(q.remove(&k40).is_some());
    q.check_invariants();
    // Removing 10 descends into the minimal left child with a minimal right
    // sibling: the fix-up must merge children around the separator.
    let k10 = q
        .debug_all_keys_in_order()
        .into_iter()
        .find(|k| k.priority == 10)
        .unwrap();
    assert!(q.remove(&k10).is_some());
    q.check_invariants();
    assert_eq!(pop_all_priorities(&mut q, 0), [20, 30]);
}

// ---------------------------------------------------------------------------
// Affinity behavior
// ---------------------------------------------------------------------------

#[test]
fn pop_for_cpu_when_no_runnable_entry_exists() {
    let mut q = Q16::new(4);
    q.push(1, mask(&[1]), 1).unwrap();
    q.push(2, mask(&[1, 3]), 2).unwrap();
    assert_eq!(q.peek_key_for_cpu(0), None);
    assert_eq!(q.pop_for_cpu(0), None);
    assert_eq!(q.pop_for_cpu(2), None);
    assert_eq!(q.len(), 2);
    q.check_invariants();
}

#[test]
fn pop_for_cpu_when_only_one_cpu_matches() {
    let mut q = Q2::new(4);
    // Entry with priority 5 is only runnable on CPU 2; entries runnable on
    // other CPUs have worse priority.
    q.push(5, mask(&[2]), 5).unwrap();
    q.push(10, mask(&[0, 1, 3]), 10).unwrap();
    let (key, affinity, _) = q.pop_for_cpu(2).unwrap();
    assert_eq!(key.priority, 5);
    assert_eq!(affinity, mask(&[2]));
    assert_eq!(q.pop_for_cpu(2), None);
    q.check_invariants();
}

#[test]
fn pop_for_cpu_with_all_cpu_affinity() {
    let mut q = Q2::new(4);
    for p in [30u32, 10, 20] {
        q.push(p, all_cpus(4), p).unwrap();
    }
    for cpu in 0..4 {
        assert_eq!(q.peek_key_for_cpu(cpu).unwrap().priority, 10);
    }
    let (key, _, _) = q.pop_for_cpu(3).unwrap();
    assert_eq!(key.priority, 10);
    q.check_invariants();
}

#[test]
fn affinity_pruning_skips_subtrees() {
    // Many CPU-0 entries with low priorities, one CPU-1 entry with the worst
    // priority: peek for CPU 1 must descend past subtrees full of CPU-0 work.
    let mut q = Q2::new(2);
    for p in 0..40u32 {
        q.push(p, mask(&[0]), p).unwrap();
    }
    let key = q.push(1000, mask(&[1]), 1000).unwrap();
    q.check_invariants();
    assert_eq!(q.peek_key_for_cpu(1), Some(key.clone()));
    assert_eq!(q.pop_for_cpu(1), Some((key, mask(&[1]), 1000)));
    assert_eq!(q.peek_key_for_cpu(1), None);
    assert_eq!(q.peek_key_for_cpu(0).unwrap().priority, 0);
    q.check_invariants();
}

#[test]
fn example_behavior_from_spec() {
    // Spec section 32.
    let mut q = Q16::new(2);
    let k10 = q.push(10, mask(&[1]), 0).unwrap();
    let k20 = q.push(20, mask(&[0, 1]), 1).unwrap();
    let _k30 = q.push(30, mask(&[0]), 2).unwrap();

    assert_eq!(q.peek_key_for_cpu(0), Some(k20.clone()));
    assert_eq!(q.peek_key_for_cpu(1), Some(k10.clone()));

    let (popped, _, _) = q.pop_for_cpu(1).unwrap();
    assert_eq!(popped, k10);

    assert_eq!(q.peek_key_for_cpu(1), Some(k20.clone()));
    assert_eq!(q.peek_key_for_cpu(0), Some(k20));
}

#[test]
fn num_cpus_64_uses_high_bits() {
    let mut q = AffinityBTreeQueue::<u32, u32, 2>::new(64);
    let key = q.push(1, mask(&[63]), 1).unwrap();
    assert_eq!(q.peek_key_for_cpu(63), Some(key));
    assert_eq!(q.peek_key_for_cpu(62), None);
    assert_eq!(q.peek_key_for_cpu(64), None);
    q.check_invariants();
}

#[test]
fn num_cpus_wide_uses_high_bits() {
    // N=2: CPUs 0..128. Exercise CPU 64 (first bit of word 1) and CPU 127.
    let mut q = AffinityBTreeQueue::<u32, u32, 2, 2>::new(128);
    let mut m64 = CpuMask::<2>::empty();
    m64.insert(64);
    let mut m127 = CpuMask::<2>::empty();
    m127.insert(127);

    let k64 = q.push(1, m64, 64).unwrap();
    let k127 = q.push(2, m127, 127).unwrap();
    q.check_invariants();

    assert_eq!(q.peek_key_for_cpu(64), Some(k64.clone()));
    assert_eq!(q.peek_key_for_cpu(127), Some(k127.clone()));
    assert_eq!(q.peek_key_for_cpu(63), None);
    assert_eq!(q.peek_key_for_cpu(128), None);

    assert_eq!(q.pop_for_cpu(64), Some((k64, m64, 64)));
    assert_eq!(q.pop_for_cpu(127), Some((k127, m127, 127)));
    assert!(q.is_empty());
    q.check_invariants();
}

// ---------------------------------------------------------------------------
// Error handling
// ---------------------------------------------------------------------------

#[test]
fn remove_nonexistent_key() {
    let mut q = Q16::new(2);
    q.push(10, mask(&[0]), 0).unwrap();
    let missing = PriorityKey {
        priority: 10u32,
        seq: 999,
    };
    assert_eq!(q.remove(&missing), None);
    assert_eq!(q.len(), 1);
    q.check_invariants();
}

#[test]
fn invalid_empty_affinity() {
    let mut q = Q16::new(4);
    assert_eq!(
        q.push(1, CpuMask::empty(), 0),
        Err(PushError::EmptyAffinity)
    );
    assert!(q.is_empty());
    q.check_invariants();
}

#[test]
fn invalid_cpu_in_affinity() {
    let mut q = Q16::new(4);
    assert_eq!(q.push(1, mask(&[4]), 0), Err(PushError::InvalidCpu));
    assert_eq!(q.push(1, mask(&[0, 5]), 0), Err(PushError::InvalidCpu));
    assert!(q.is_empty());
    q.check_invariants();
}

#[test]
fn sequence_overflow_is_rejected() {
    let mut q = Q16::new(2);
    q.debug_set_next_seq(u64::MAX - 1);
    let key = q.push(1, mask(&[0]), 0).unwrap();
    assert_eq!(key.seq, u64::MAX - 1);
    assert_eq!(q.push(2, mask(&[0]), 1), Err(PushError::SequenceOverflow));
    assert_eq!(q.len(), 1);
    q.check_invariants();
}

// ---------------------------------------------------------------------------
// Generic priority types
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ClassPriority {
    class: u8,
    sub: u8,
}

impl Ord for ClassPriority {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.class
            .cmp(&other.class)
            .then_with(|| self.sub.cmp(&other.sub))
    }
}

impl PartialOrd for ClassPriority {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[test]
fn custom_priority_type_implementing_ord() {
    let mut q = AffinityBTreeQueue::<ClassPriority, u32, 2>::new(2);
    let inputs = [
        ClassPriority { class: 2, sub: 0 },
        ClassPriority { class: 0, sub: 9 },
        ClassPriority { class: 1, sub: 1 },
        ClassPriority { class: 0, sub: 3 },
        ClassPriority { class: 1, sub: 0 },
    ];
    for (i, p) in inputs.iter().enumerate() {
        q.push(*p, mask(&[0]), i as u32).unwrap();
        q.check_invariants();
    }
    let mut sorted = inputs;
    sorted.sort();
    for expected in sorted {
        let (key, _, _) = q.pop_for_cpu(0).unwrap();
        assert_eq!(key.priority, expected);
        q.check_invariants();
    }
}

#[test]
fn reverse_priority_ordering() {
    let mut q = AffinityBTreeQueue::<Reverse<u32>, u32, 2>::new(2);
    for p in [10u32, 30, 20] {
        q.push(Reverse(p), mask(&[0]), p).unwrap();
        q.check_invariants();
    }
    // With Reverse, larger raw values dequeue first.
    let mut popped = Vec::new();
    while let Some((key, _, _)) = q.pop_for_cpu(0) {
        popped.push(key.priority.0);
        q.check_invariants();
    }
    assert_eq!(popped, [30, 20, 10]);
}

// ---------------------------------------------------------------------------
// Randomized property tests against the reference model (spec section 28)
// ---------------------------------------------------------------------------

fn random_mask<const N: usize>(rng: &mut XorShift64, num_cpus: usize) -> CpuMask<N> {
    let mut m = CpuMask::empty();
    let num_words = (num_cpus + 63).div_ceil(64);
    for w in 0..num_words.min(N) {
        let first_cpu = w * 64;
        let last_cpu = ((w + 1) * 64).min(num_cpus);
        let bits_count = last_cpu - first_cpu;
        let allowed = if bits_count >= 64 {
            u64::MAX
        } else {
            (1u64 << bits_count) - 1
        };
        let bits = rng.next() & allowed;
        m.set_word(w, bits);
    }
    if m.is_empty() {
        let cpu = (rng.next() as usize) % num_cpus;
        m.insert(cpu);
    }
    m
}

fn run_random_ops<const T: usize, const N: usize>(num_cpus: usize, seed: u64, num_ops: usize) {
    let mut rng = XorShift64::new(seed);
    let mut q = AffinityBTreeQueue::<u32, u32, T, N>::new(num_cpus);
    let mut model = RefModel::<u32, u32, N>::new(num_cpus);

    for op_index in 0..num_ops {
        match rng.next() % 6 {
            // Push half the time so trees grow into multiple levels.
            0..=2 => {
                let priority = (rng.next() % 64) as u32;
                let affinity = random_mask(&mut rng, num_cpus);
                let value = op_index as u32;
                assert_eq!(
                    q.push(priority, affinity, value),
                    model.push(priority, affinity, value)
                );
            }
            3 => {
                let cpu = (rng.next() as usize) % num_cpus;
                assert_eq!(q.pop_for_cpu(cpu), model.pop_for_cpu(cpu));
            }
            4 => {
                if !model.entries.is_empty() {
                    let idx = (rng.next() as usize) % model.entries.len();
                    let key = model.entries[idx].key.clone();
                    assert_eq!(q.remove(&key), model.remove(&key));
                }
            }
            _ => {
                let key = PriorityKey {
                    priority: (rng.next() % 64) as u32,
                    seq: rng.next() % 64,
                };
                assert_eq!(q.remove(&key), model.remove(&key));
            }
        }

        q.check_invariants();
        assert_eq!(q.len(), model.len());
        assert_eq!(q.debug_count_entries(), model.len());
        for cpu in 0..num_cpus {
            assert_eq!(
                q.peek_key_for_cpu(cpu),
                model.peek_key_for_cpu(cpu),
                "peek mismatch for cpu {cpu}"
            );
        }
        assert_eq!(q.debug_all_entries_in_order(), model.entries_in_order());
    }
}

#[test]
fn random_ops_1_cpu() {
    for seed in 0..30 {
        run_random_ops::<16, 1>(1, seed, 1000);
    }
}

#[test]
fn random_ops_2_cpus() {
    for seed in 100..125 {
        run_random_ops::<16, 1>(2, seed, 1000);
    }
}

#[test]
fn random_ops_4_cpus() {
    for seed in 200..220 {
        run_random_ops::<16, 1>(4, seed, 1000);
    }
}

#[test]
fn random_ops_8_cpus() {
    for seed in 300..315 {
        run_random_ops::<16, 1>(8, seed, 1000);
    }
}

#[test]
fn random_ops_16_cpus() {
    for seed in 400..407 {
        run_random_ops::<16, 1>(16, seed, 1000);
    }
}

#[test]
fn random_ops_64_cpus() {
    for seed in 500..503 {
        run_random_ops::<16, 1>(64, seed, 1000);
    }
}

#[test]
fn random_ops_degree_2() {
    // T=2 reaches splits, merges, borrows, and root shrink constantly.
    for seed in 600..620 {
        run_random_ops::<2, 1>(4, seed, 600);
    }
}

#[test]
fn random_ops_degree_3() {
    for seed in 700..710 {
        run_random_ops::<3, 1>(4, seed, 600);
    }
}

#[test]
fn random_ops_narrow_cpu_count_degree_2() {
    // T=2, N=1, 8 CPUs: exercises low CPU count with many structural changes.
    for seed in 800..815 {
        run_random_ops::<2, 1>(8, seed, 600);
    }
}

#[test]
fn random_ops_narrow_cpu_count_degree_16() {
    for seed in 900..905 {
        run_random_ops::<16, 1>(16, seed, 800);
    }
}

#[test]
fn random_ops_n2_65_cpus() {
    // N=2: first test that crosses the 64-CPU boundary.
    for seed in 1000..1010 {
        run_random_ops::<2, 2>(65, seed, 600);
    }
}

#[test]
fn random_ops_n2_128_cpus() {
    // N=2: full 128-CPU mask exercises both words of CpuMask<2>.
    for seed in 1100..1105 {
        run_random_ops::<16, 2>(128, seed, 800);
    }
}

// ---------------------------------------------------------------------------
// Invariant violation (defensive panic paths)
// ---------------------------------------------------------------------------

#[test]
#[should_panic(expected = "subtree_affinity invariant is broken")]
fn broken_subtree_affinity_internal_node_panics() {
    let mut q: Q2 = AffinityBTreeQueue::new(2);
    // Insert 4 entries to force a root split (root becomes internal with T=2).
    for i in 1u32..=4 {
        q.push(i, mask(&[0]), i).unwrap();
    }
    // Corrupt the root's subtree_affinity to claim CPU 1 is present.
    let root_id = q.root.unwrap();
    q.nodes[root_id.0]
        .as_mut()
        .unwrap()
        .subtree_affinity
        .insert(1);
    // pop_for_cpu(1): at the internal root, all children and entries are CPU 0
    // only, so the rightmost-child block (lines 584-590) is entered but the
    // inner condition is false → falls through to panic.
    let _ = q.pop_for_cpu(1);
}

#[test]
#[should_panic(expected = "subtree_affinity invariant is broken")]
fn broken_subtree_affinity_leaf_node_panics() {
    let mut q: Q2 = AffinityBTreeQueue::new(2);
    // Single entry: root is a leaf.
    q.push(1, mask(&[0]), 1).unwrap();
    // Corrupt the leaf root's subtree_affinity to claim CPU 1 is present.
    let root_id = q.root.unwrap();
    q.nodes[root_id.0]
        .as_mut()
        .unwrap()
        .subtree_affinity
        .insert(1);
    // pop_for_cpu(1): the for loop exhausts all leaf entries, the outer
    // `if !x.leaf` is skipped (leaf), falls straight to panic.
    let _ = q.pop_for_cpu(1);
}

// ---------------------------------------------------------------------------
// RefModel error paths
// ---------------------------------------------------------------------------

#[test]
fn ref_model_push_empty_affinity() {
    let mut model: RefModel<u32, u32> = RefModel::new(4);
    assert_eq!(
        model.push(1, CpuMask::empty(), 0),
        Err(PushError::EmptyAffinity)
    );
}

#[test]
fn ref_model_push_invalid_cpu() {
    let mut model: RefModel<u32, u32> = RefModel::new(4);
    // CPU 4 >= num_cpus(4) → InvalidCpu
    assert_eq!(model.push(1, mask(&[4]), 0), Err(PushError::InvalidCpu));
}

#[test]
fn ref_model_pop_out_of_range_cpu_returns_none() {
    let mut model: RefModel<u32, u32> = RefModel::new(4);
    model.push(1, mask(&[0]), 0).unwrap();
    // CPU 4 >= num_cpus(4): peek_key_for_cpu returns None
    assert_eq!(model.pop_for_cpu(4), None);
}
