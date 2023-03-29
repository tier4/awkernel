#![no_std]

use core::{cell::Cell, marker::PhantomData};

use alloc::rc::Rc;

pub mod arch;
pub mod cpu;
pub mod delay;
pub mod logger;
pub mod mmio;

extern crate alloc;

pub type PhantomUnsync = PhantomData<Cell<()>>;
pub type PhantomUnsend = PhantomData<Rc<()>>;
