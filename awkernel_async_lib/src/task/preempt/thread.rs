use alloc::{
    boxed::Box,
    collections::{BTreeMap, VecDeque},
};
use awkernel_lib::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    context::{ArchContext, Context},
    memory::{self, PAGESIZE},
    sync::mutex::{MCSNode, Mutex},
    unwind::catch_unwind,
};
use core::alloc::{GlobalAlloc, Layout};

/// Pooled and running threads.
static THREADS: Mutex<Threads> = Mutex::new(Threads::new());

struct Threads {
    pooled: VecDeque<PtrWorkerThreadContext>,
    running: BTreeMap<usize, PtrWorkerThreadContext>,
}

impl Threads {
    const fn new() -> Self {
        Threads {
            pooled: VecDeque::new(),
            running: BTreeMap::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PtrWorkerThreadContext(*mut WorkerThreadContext);

unsafe impl Sync for PtrWorkerThreadContext {}
unsafe impl Send for PtrWorkerThreadContext {}

impl PtrWorkerThreadContext {
    pub fn new() -> Self {
        let ctx = Box::new(WorkerThreadContext::new());
        let ptr = Box::into_raw(ctx);
        PtrWorkerThreadContext(ptr)
    }

    /// # Safety
    ///
    /// `ctx` must be a pointer of `WorkerThreadContext`.
    pub unsafe fn with_context(ctx: usize) -> Self {
        let ptr = ctx as *mut WorkerThreadContext;
        PtrWorkerThreadContext(ptr)
    }

    pub fn with_stack_and_entry(
        stack_size: usize,
        entry: extern "C" fn(usize) -> !,
        arg: usize,
    ) -> Result<Self, &'static str> {
        let ctx = WorkerThreadContext::with_stack_and_entry(stack_size, entry, arg)?;
        let ptr_ctx = Box::new(ctx);
        let ptr = Box::into_raw(ptr_ctx);
        Ok(PtrWorkerThreadContext(ptr))
    }

    unsafe fn delete(self) {
        let ctx = Box::from_raw(self.0);
        unsafe {
            memory::map(
                ctx.stack_mem,
                ctx.stack_mem_phy,
                memory::Flags {
                    execute: false,
                    write: true,
                },
            )
        };
    }

    pub unsafe fn set_argument(&mut self, arg: usize) {
        let ptr = &mut *self.0;
        ptr.cpu_ctx.set_argument(arg);
    }

    pub fn get_cpu_context_mut(&mut self) -> &mut ArchContext {
        let ptr = unsafe { &mut *self.0.cast::<WorkerThreadContext>() };
        &mut ptr.cpu_ctx
    }

    pub fn get_cpu_context(&self) -> &ArchContext {
        let ptr = unsafe { &*self.0.cast::<WorkerThreadContext>() };
        &ptr.cpu_ctx
    }
}

struct WorkerThreadContext {
    cpu_ctx: ArchContext,
    stack_mem: VirtAddr,
    stack_mem_phy: PhyAddr,
    stack_size: usize,
}

impl WorkerThreadContext {
    fn new() -> Self {
        WorkerThreadContext {
            cpu_ctx: ArchContext::default(),
            stack_mem: VirtAddr::new(0),
            stack_mem_phy: PhyAddr::new(0),
            stack_size: 0,
        }
    }

    fn with_stack_and_entry(
        stack_size: usize,
        entry: extern "C" fn(usize) -> !,
        arg: usize,
    ) -> Result<Self, &'static str> {
        let stack_mem = allocate_stack(stack_size)?;
        let stack_pointer = unsafe { stack_mem.add(stack_size) };

        let Some(stack_mem_phy) = memory::vm_to_phy(VirtAddr::new(stack_mem as usize)) else {
            return Err("failed to translate VM to Phy");
        };

        let stack_mem = VirtAddr::new(stack_mem as usize);

        unsafe { memory::unmap(stack_mem) };

        let mut cpu_ctx = ArchContext::default();

        unsafe {
            cpu_ctx.set_stack_pointer(stack_pointer as usize);
            cpu_ctx.set_entry_point(entry, arg);
        }

        Ok(WorkerThreadContext {
            cpu_ctx,
            stack_mem,
            stack_mem_phy,
            stack_size,
        })
    }
}

impl Drop for WorkerThreadContext {
    fn drop(&mut self) {
        if self.stack_mem.to_usize() != 0 {
            let layout = Layout::from_size_align(self.stack_size, PAGESIZE).unwrap();
            unsafe {
                awkernel_lib::heap::TALLOC.dealloc(self.stack_mem.to_usize() as *mut u8, layout)
            };
        }
    }
}

fn allocate_stack(size: usize) -> Result<*mut u8, &'static str> {
    let Ok(layout) = Layout::from_size_align(size, PAGESIZE) else {
        return Err("invalid layout");
    };

    let result = catch_unwind(|| unsafe {
        let _config = awkernel_lib::heap::TALLOC.save();
        awkernel_lib::heap::TALLOC.use_primary();
        awkernel_lib::heap::TALLOC.alloc(layout)
    });

    match result {
        Ok(ptr) => {
            assert_eq!(ptr as usize & (PAGESIZE - 1), 0);
            Ok(ptr)
        }
        Err(_) => Err("failed to allocate stack memory"),
    }
}

/// Take a pooled thread.
pub(super) fn take_pooled_thread() -> Option<PtrWorkerThreadContext> {
    let mut node = MCSNode::new();
    let mut threads = THREADS.lock(&mut node);
    threads.pooled.pop_front()
}

/// Create a thread whose entry is `entry` with `arg` as the first argument.
pub(super) fn create_thread(
    entry: extern "C" fn(usize) -> !,
    arg: usize,
) -> Result<PtrWorkerThreadContext, &'static str> {
    PtrWorkerThreadContext::with_stack_and_entry(1024 * 1024 * 2, entry, arg)
}

/// Make `thread` pooled.
pub(super) fn make_thread_pooled(thread: PtrWorkerThreadContext) {
    let mut node = MCSNode::new();
    let mut threads = THREADS.lock(&mut node);
    threads.pooled.push_front(thread);
}

/// Deallocate all pooled thread.
pub fn deallocate_thread_pool() {
    let mut node = MCSNode::new();
    let mut threads = THREADS.lock(&mut node);

    while let Some(thread) = threads.pooled.pop_front() {
        unsafe { thread.delete() };
    }
}

/// Set `ctx` as the context running currently.
pub fn set_current_context(ctx: PtrWorkerThreadContext) {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    let mut node = MCSNode::new();
    let mut threads = THREADS.lock(&mut node);

    // must empty
    assert!(threads.running.insert(cpu_id, ctx).is_none())
}

/// Take the current context.
pub fn take_current_context() -> PtrWorkerThreadContext {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    let mut node = MCSNode::new();
    let mut threads = THREADS.lock(&mut node);

    // must not empty
    threads.running.remove(&cpu_id).unwrap()
}
