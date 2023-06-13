//! The delta list was originally introduced by [Operating System Design, The Xinu Approach](https://xinu.cs.purdue.edu/)'s
//! Chapter 13.
//!
//! We specified the delta list by using TLA+.
//! See [the specification](https://github.com/tier4/safe_drive/tree/main/specifications/callback).

use alloc::boxed::Box;
use core::cell::UnsafeCell;

/// Timers are represented by a linked list.
/// Each element represents the difference of time from parent node.
///
/// For example, if `timer = 10 -> 20 -> 5`,
/// timers will be invoked after 10, 10 + 20 = 30, and 10 + 20 + 5 = 35 seconds later, respectively.
///
/// At that time, if `t` is 13, the callback will be invoked 13 seconds later.
/// To accomplish this, 13 should be inserted between 10 and 20 like
/// `10 -> 3 (inserted) -> 17 (updated) -> 5`.
pub enum DeltaList<T> {
    Cons(Box<UnsafeCell<(u64, T, DeltaList<T>)>>),
    Nil,
}

impl<T> DeltaList<T> {
    /// Insert a data which will be invoked after `dur` duration.
    ///
    /// For example, if a delta list is `10 -> 20 -> 5`,
    /// and a duration of `15` is inserted,
    /// the list is updated to `10 -> 5 -> 15 -> 5`.
    pub fn insert(&mut self, dur: u64, data: T) {
        insert_delta(self, dur, data);
    }

    pub fn front(&self) -> Option<(u64, &T)> {
        if let DeltaList::Cons(e) = self {
            let elm = unsafe { &(*e.get()) };
            Some((elm.0, &elm.1))
        } else {
            None
        }
    }

    pub fn pop(&mut self) -> Option<Self> {
        if let DeltaList::Cons(e) = self {
            let next = core::mem::replace(&mut e.get_mut().2, DeltaList::Nil);
            let head = core::mem::replace(self, next);
            Some(head)
        } else {
            None
        }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, DeltaList::Nil)
    }
}

fn insert_delta<T>(mut list: &mut DeltaList<T>, mut delta: u64, data: T) {
    loop {
        match list {
            DeltaList::Nil => {
                *list = DeltaList::Cons(Box::new(UnsafeCell::new((delta, data, DeltaList::Nil))));
                return;
            }
            DeltaList::Cons(e) => {
                let front = e.get();
                let d_mut = unsafe { &mut (*front).0 };
                if delta < *d_mut {
                    *d_mut -= delta;
                    let next = core::mem::replace(list, DeltaList::Nil);
                    *list = DeltaList::Cons(Box::new(UnsafeCell::new((delta, data, next))));
                    return;
                } else {
                    delta -= *d_mut;
                    list = unsafe { &mut (*front).2 };
                }
            }
        }
    }
}

#[cfg(kani)]
mod verification {
    use super::*;
    use alloc::vec::Vec;

    #[kani::proof]
    #[kani::unwind(4)]
    fn verify_delta_list() {
        let size: usize = 3;
        let mut dlist = DeltaList::<u32>::Nil;
        let mut vec = Vec::new();
        for _ in 0..size {
            let val: u64 = kani::any();
            dlist.insert(val, 0);
            vec.push(val);
        }
    
        vec.sort();
        let mut tmp = vec[0];
        for i in 1..size {
            let tmp2 = vec[i];
            vec[i] = vec[i] - tmp;
            tmp = tmp2;
        }
    
        let mut idx = 0;
        while let Some((t, _)) = dlist.front() {
            assert!(vec[idx] == t);
            dlist.pop();
            idx += 1;
        }
    }
}