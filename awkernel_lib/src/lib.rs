#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "std", feature(thread_local))]
#![feature(allocator_api)]

use core::{cell::Cell, marker::PhantomData};

use alloc::rc::Rc;

pub mod addr;
pub mod arch;
pub mod config;
pub mod console;
pub mod cpu;
pub mod delay;
pub mod device_tree;
pub mod dvfs;
pub mod graphics;
pub mod interrupt;
pub mod local_heap;
pub mod logger;
pub mod mmio;
pub mod net;
pub mod ntp;
pub mod priority_queue;
pub mod sanity;
pub mod sync;
pub mod time;
pub mod timer;
pub mod unwind;

#[cfg(not(feature = "std"))]
pub mod heap;

#[cfg(not(feature = "std"))]
pub mod dma_pool;

#[cfg(not(feature = "std"))]
pub mod context;

pub mod paging;

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
