use crate::task::catch_unwind;
use alloc::{
    collections::{BTreeMap, LinkedList},
    sync::Arc,
};
use awkernel_lib::{
    context::{ArchContext, Context},
    memory::PAGESIZE,
    sync::mutex::{MCSNode, Mutex},
};
use core::{
    alloc::{GlobalAlloc, Layout},
    ptr::null_mut,
};

static THREADS: Mutex<Threads> = Mutex::new(Threads::new());

struct Threads {
    pool: LinkedList<PtrWorkerThreadContext>,
    running: BTreeMap<usize, PtrWorkerThreadContext>,
}

#[derive(Debug, Clone, Copy)]
pub struct PtrWorkerThreadContext(*mut WorkerThreadContext);

unsafe impl Sync for PtrWorkerThreadContext {}
unsafe impl Send for PtrWorkerThreadContext {}

impl Threads {
    const fn new() -> Self {
        Threads {
            pool: LinkedList::new(),
            running: BTreeMap::new(),
        }
    }
}

pub fn yield_to(ptr: PtrWorkerThreadContext) {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    let ctx = {
        let mut node = MCSNode::new();
        let threads = THREADS.lock(&mut node);
        let ctx = threads.running.get(&cpu_id).unwrap();
        ctx.0 as *const ArchContext as *mut ArchContext
    };

    let result = unsafe {
        let ctx = &mut *ctx as &mut ArchContext;
        ctx.set_jump()
    };

    if result {
    } else {
    }
}

fn save_context() -> bool {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    let ctx = {
        let mut node = MCSNode::new();
        let threads = THREADS.lock(&mut node);
        let ctx = threads.running.get(&cpu_id).unwrap();
        ctx.0 as *const ArchContext as *mut ArchContext
    };

    unsafe {
        let ctx = &mut *ctx as &mut ArchContext;
        ctx.set_jump()
    }
}

pub struct WorkerThreadContext {
    cpu_ctx: ArchContext,
    stack_mem: *mut u8,
    stack_size: usize,
}

impl WorkerThreadContext {
    pub fn new() -> Self {
        WorkerThreadContext {
            cpu_ctx: ArchContext::default(),
            stack_mem: null_mut(),
            stack_size: 0,
        }
    }

    pub fn with_stack(stack_size: usize) -> Result<Self, &'static str> {
        let stack_mem = allocate_stack(stack_size)?;

        Ok(WorkerThreadContext {
            cpu_ctx: ArchContext::default(),
            stack_mem,
            stack_size,
        })
    }

    pub fn with_context_and_stack(
        ctx: &ArchContext,
        stack_size: usize,
    ) -> Result<Self, &'static str> {
        let stack_mem = allocate_stack(stack_size)?;

        Ok(WorkerThreadContext {
            cpu_ctx: *ctx,
            stack_mem,
            stack_size,
        })
    }

    pub fn stack_start(&self) -> *mut () {
        let ptr = unsafe { self.stack_mem.add(self.stack_size) };
        ptr as _
    }
}

impl Drop for WorkerThreadContext {
    fn drop(&mut self) {
        if !self.stack_mem.is_null() {
            let layout = Layout::from_size_align(self.stack_size, PAGESIZE).unwrap();
            unsafe { awkernel_lib::heap::TALLOC.dealloc(self.stack_mem, layout) };
        }
    }
}

fn allocate_stack(size: usize) -> Result<*mut u8, &'static str> {
    let Ok(layout) = Layout::from_size_align(size, PAGESIZE) else {
        return Err("invalid layout")
    };

    let result = catch_unwind(|| unsafe {
        let _config = awkernel_lib::heap::TALLOC.save();
        awkernel_lib::heap::TALLOC.use_primary();
        awkernel_lib::heap::TALLOC.alloc(layout)
    });

    match result {
        Ok(ptr) => Ok(ptr),
        Err(_) => Err("failed to allocate stack memory"),
    }
}
