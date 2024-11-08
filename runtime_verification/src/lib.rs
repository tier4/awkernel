#![no_std]

extern crate alloc;

pub mod event;
pub mod model;
mod state;

use alloc::collections::btree_map::BTreeMap;
use awkernel_lib::sync::mutex::Mutex;

pub static MODELS: Mutex<BTreeMap<u32, crate::model::TaskModel>> = Mutex::new(BTreeMap::new());
