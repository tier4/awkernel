#![no_std]
#![feature(core_intrinsics)]

use core::{cell::Cell, marker::PhantomData};

use alloc::rc::Rc;

pub mod arch;
pub mod cpu;
pub mod delay;
pub mod logger;
pub mod mmio;

#[cfg(not(feature = "std"))]
pub mod heap;

extern crate alloc;

pub type PhantomUnsync = PhantomData<Cell<()>>;
pub type PhantomUnsend = PhantomData<Rc<()>>;
