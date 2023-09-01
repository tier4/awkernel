#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "std", feature(thread_local))]
#![feature(core_intrinsics)]
#![feature(allocator_api)]

use core::{cell::Cell, marker::PhantomData};

use alloc::rc::Rc;
use sync::mutex::Mutex;

pub mod arch;
pub mod console;
pub mod cpu;
pub mod delay;
pub mod device_tree;
pub mod interrupt;
pub mod local_heap;
pub mod logger;
pub mod mmio;
pub mod net;
pub mod sanity;
pub mod sync;
pub mod timer;
pub mod unwind;

#[cfg(not(feature = "std"))]
pub mod heap;

#[cfg(not(feature = "std"))]
pub mod context;

#[cfg(not(feature = "std"))]
pub mod memory;

extern crate alloc;

pub type PhantomUnsync = PhantomData<Cell<()>>;
pub type PhantomUnsend = PhantomData<Rc<()>>;

#[cfg(feature = "std")]
pub const IS_STD: bool = true;

#[cfg(not(feature = "std"))]
pub const IS_STD: bool = false;

#[macro_export]
macro_rules! err_msg {
    ($m:expr) => {
        concat!(file!(), ":", line!(), ":", column!(), ": ", $m)
    };
}

// POLL_TIMESTAMPS[i] contains the Start poll() save_time and End poll() restore_time of the poll() call in i-th CPU.
pub static POLL_TIMESTAMPS: [Mutex<(u64, u64)>; 32] = [
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
    Mutex::new((0, 0)),
];
