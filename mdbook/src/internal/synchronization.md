# Synchronization

The [awkernel_lib/src/sync.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/sync.rs) module provides synchronization primitives.
[`Mutex`:awkernel_lib/src/sync/mutex.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/sync/mutex.rs) is used for mutual exclusion.
[`RwLock`:awkernel_lib/src/sync/rwlock.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/sync/rwlock.rs) is used for read-write locks.
Note that these locks are spin-based, and interrupts are disabled during the critical section.

## Mutex

Awkernel adopts MCS lock [1] for mutual exclusion by default
because the safety and liveliness of MCS lock have been formally verified [2].
Therefore, `MCSNode` have to be used when using `Mutex` as follows.

```rust
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use alloc::sync::Arc;

let data = Arc::new(Mutex::new(0));

// acquire the lock
let mut node = MCSNode::new();
let guard = data.lock(&mut node);

*guard = 10;
```

## RwLock

`RwLock` can be used as normal read-write lock as follows.

```rust
use awkernel_lib::sync::rwlock::RwLock;
use alloc::sync::Arc;

let data = Arc::new(RwLock::new(0));

{
    // write lock
    let guard = data.write();
    *guard = 10;
}

{
    // read lock
    let guard = data.read();
    assert_eq!(*guard, 10);
}
```

## References

1. J. M. Mellor-Crummey and M. L. Scott. Algorithms for scalable synchronization on shared-
memory multiprocessors. ACM Trans. Comput. Syst., 9(1), Feb. 1991.
2. J. Kim, V. Sjöberg, R. Gu, Z. Shao. Safety and Liveness of MCS Lock - Layer by Layer. APLAS 2017: 273-297
