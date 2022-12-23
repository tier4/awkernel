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
    /// Insert a data which will be invoked after `delta` duration.
    ///
    /// For example, if a delta list is `10 -> 20 -> 5`,
    /// and a delta of `15` is inserted,
    /// the list is updated to `10 -> 5 -> 5 -> 5`.
    pub fn insert(&mut self, delta: u64, data: T) {
        insert_delta(self, delta, data);
    }

    pub fn front(&self) -> Option<(u64, &T)> {
        if let DeltaList::Cons(e) = self {
            let elm = unsafe { &(*e.get()) };
            Some((elm.0, &elm.1))
        } else {
            None
        }
    }

    pub fn front_mut(&mut self) -> Option<(&mut u64, &mut T)> {
        if let DeltaList::Cons(e) = self {
            let elm = e.get_mut();
            Some((&mut elm.0, &mut elm.1))
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

    pub fn filter<U>(&mut self, f: U)
    where
        U: Fn(&T) -> bool,
    {
        filter_delta(self, f);
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

fn filter_delta<T, U>(mut list: &mut DeltaList<T>, f: U)
where
    U: Fn(&T) -> bool,
{
    loop {
        match list {
            DeltaList::Nil => {
                return;
            }
            DeltaList::Cons(e) => {
                let front = e.get();
                let d_mut = unsafe { &mut (*front).1 };
                if f(d_mut) {
                    list = unsafe { &mut (*front).2 };
                } else {
                    let next = unsafe { &mut (*front).2 };
                    let next = core::mem::replace(next, DeltaList::Nil);
                    *list = next;
                }
            }
        }
    }
}
