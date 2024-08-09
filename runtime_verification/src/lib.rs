#![no_std]

extern crate alloc;

pub mod event;
mod model;
pub mod task;

use alloc::collections::btree_map::BTreeMap;
use awkernel_lib::sync::mutex::Mutex;

pub static MODELS: Mutex<BTreeMap<u32, crate::task::TaskModel>> = Mutex::new(BTreeMap::new());
