use crate::task::{catch_unwind, Task};
use alloc::{
    boxed::Box,
    collections::{BTreeMap, BTreeSet, LinkedList},
    sync::Arc,
};
use awkernel_lib::{
    context::{ArchContext, Context},
    interrupt::{self, InterruptGuard},
    memory::PAGESIZE,
    sync::mutex::{MCSNode, Mutex},
};
use core::{
    alloc::{GlobalAlloc, Layout},
    ptr::null_mut,
};
use futures::task::ArcWake;

static THREADS: Mutex<Threads> = Mutex::new(Threads::new());

struct Threads {
    pooled: LinkedList<PtrWorkerThreadContext>,
    running: BTreeMap<usize, PtrWorkerThreadContext>,
    preempted: BTreeSet<PtrWorkerThreadContext>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct PtrWorkerThreadContext(*mut WorkerThreadContext);

unsafe impl Sync for PtrWorkerThreadContext {}
unsafe impl Send for PtrWorkerThreadContext {}

impl PtrWorkerThreadContext {
    fn new() -> Self {
        let ctx = Box::new(WorkerThreadContext::new());
        let ptr = Box::into_raw(ctx);
        PtrWorkerThreadContext(ptr)
    }

    unsafe fn delete(ptr: PtrWorkerThreadContext) {
        let _ctx = Box::from_raw(ptr.0);
    }
}

impl Threads {
    const fn new() -> Self {
        Threads {
            pooled: LinkedList::new(),
            running: BTreeMap::new(),
            preempted: BTreeSet::new(),
        }
    }
}

/// Yield to `ptr`.
/// Current thread will be the pooled state,
/// and `ptr` will be the running state.
pub(crate) unsafe fn yield_and_pool(ptr: PtrWorkerThreadContext) {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    let ctx = {
        let mut node = MCSNode::new();
        let mut threads = THREADS.lock(&mut node);
        let ctx = threads.running.get(&cpu_id).unwrap();
        let ctx = *ctx;

        threads.running.insert(cpu_id, ptr);
        threads.pooled.push_back(ctx);

        ctx.0 as *const ArchContext as *mut ArchContext
    };

    unsafe {
        let ctx = &mut *ctx as &mut ArchContext;
        if !ctx.set_jump() {
            let target = &*ptr.0;
            target.cpu_ctx.long_jump();
        }
    }
}

/// Yield to `ptr`.
/// Current thread will be the preempted state.
/// and `ptr` will be the running state.
pub(crate) fn yield_and_preempted(ptr: PtrWorkerThreadContext, task: Arc<Task>) {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    // Disable interrupt.
    let _int_guard = InterruptGuard::new();
    interrupt::disable();

    let ctx = {
        let mut node = MCSNode::new();
        let mut threads = THREADS.lock(&mut node);
        let ctx = threads.running.get(&cpu_id).unwrap();
        let ctx = *ctx;

        threads.running.insert(cpu_id, ptr);
        threads.preempted.insert(ctx);

        ctx.0 as *const ArchContext as *mut ArchContext
    };

    unsafe {
        let ctx = &mut *ctx as &mut ArchContext;
        if !ctx.set_jump() {
            // Re-schedule.
            task.wake();

            let target = &*ptr.0;
            target.cpu_ctx.long_jump();
        }
    }
}

struct WorkerThreadContext {
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

pub fn init(cpu_id: usize) {
    let ctx = PtrWorkerThreadContext::new();

    let mut node = MCSNode::new();
    let mut threads = THREADS.lock(&mut node);

    threads.running.insert(cpu_id, ctx);
}

pub fn current_context() -> PtrWorkerThreadContext {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    let mut node = MCSNode::new();
    let threads = THREADS.lock(&mut node);

    *threads.running.get(&cpu_id).unwrap()
}
