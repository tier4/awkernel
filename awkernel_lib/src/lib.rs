#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "std", feature(thread_local))]
#![feature(core_intrinsics)]

use core::{cell::Cell, marker::PhantomData};

use alloc::rc::Rc;

pub mod arch;
pub mod console;
pub mod cpu;
pub mod delay;
pub mod interrupt;
pub mod logger;
pub mod mmio;
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
