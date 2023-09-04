#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "std", feature(thread_local))]
#![feature(core_intrinsics)]
#![feature(allocator_api)]

use core::{cell::Cell, marker::PhantomData};

use alloc::rc::Rc;
use cpu::NUM_MAX_CPU;

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

pub const DURATION: usize = 100000;
// POLL_TIMESTAMPS[i] contains the Start poll() save_time and End poll() restore_time of the poll() call in i-th CPU.
pub static mut POLL_TIMESTAMPS: [(u64, u64); NUM_MAX_CPU] = [(0, 0); NUM_MAX_CPU];
// Where SWITCH_TIME[0][i] is the min, SWITCH_TIME[1][i] is the ave, and SWITCH_TIME[2][i] is the max for the i-th CPU.
pub static mut SWITCH_TIME: [[f64; NUM_MAX_CPU]; 3] = [[0.0; NUM_MAX_CPU]; 3];
