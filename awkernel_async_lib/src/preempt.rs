use crate::task::{Task, TaskList};
use alloc::{
    boxed::Box,
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::Arc,
};
use array_macro::array;
use awkernel_lib::{
    context::{ArchContext, Context},
    cpu::NUM_MAX_CPU,
    interrupt::InterruptGuard,
    memory::{self, Flags, PAGESIZE},
    sync::mutex::{MCSNode, Mutex},
    unwind::catch_unwind,
};
use core::{
    alloc::{GlobalAlloc, Layout},
    ptr::null_mut,
};
use futures::task::ArcWake;

static THREADS: Mutex<Threads> = Mutex::new(Threads::new());
static TASKS: [Mutex<TaskList>; NUM_MAX_CPU] =
    array![_ => Mutex::new(TaskList::new()); NUM_MAX_CPU];

struct Threads {
    pooled: VecDeque<PtrWorkerThreadContext>,
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

    fn with_stack_and_entry(
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
                ctx.stack_mem as usize,
                ctx.stack_mem_phy,
                Flags {
                    execute: false,
                    write: true,
                },
            )
        };
    }
}

impl Threads {
    const fn new() -> Self {
        Threads {
            pooled: VecDeque::new(),
            running: BTreeMap::new(),
            preempted: BTreeSet::new(),
        }
    }
}

/// The current thread yields to `ptr` and it is pooled.
pub(crate) unsafe fn yield_and_pool(ptr: PtrWorkerThreadContext) {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    let ctx = {
        let mut node = MCSNode::new();
        let mut threads = THREADS.lock(&mut node);
        let ctx = threads.running.get(&cpu_id).unwrap();
        let ctx = *ctx;

        threads.running.insert(cpu_id, ptr);
        threads.pooled.push_front(ctx);

        ctx.0 as *const ArchContext as *mut ArchContext
    };

    unsafe {
        let ctx = &mut *ctx as &mut ArchContext;
        let target = &*ptr.0;

        if !Context::set_jump(ctx) {
            target.cpu_ctx.long_jump();
        } else {
            re_schedule();
        }
    }
}

/// The thread of `current_task` yields to `next_thread`.
/// The current thread will be preempted, and waked soon.
pub(crate) fn yield_preempted_and_wake_task(
    next_thread: PtrWorkerThreadContext,
    current_task: Arc<Task>,
) {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    // Disable interrupt.
    let _int_guard = InterruptGuard::new();

    let current_ctx = {
        let mut node = MCSNode::new();
        let mut threads = THREADS.lock(&mut node);
        let ctx = threads.running.get(&cpu_id).unwrap();
        let ctx = *ctx;

        threads.running.insert(cpu_id, next_thread);
        threads.preempted.insert(ctx);

        ctx.0 as *const ArchContext as *mut ArchContext
    };

    {
        // The current task will be re-scheduled.
        let mut node = MCSNode::new();
        let mut tasks = TASKS[cpu_id].lock(&mut node);
        tasks.push(current_task);
    }

    unsafe {
        // Save the current context.
        let ctx = &mut *current_ctx as &mut ArchContext;

        if !Context::set_jump(ctx) {
            // Jump to the next thread.
            let target = &*next_thread.0;
            target.cpu_ctx.long_jump();
        } else {
            re_schedule();
        }
    }
}

pub fn re_schedule() {
    let cpu_id = awkernel_lib::cpu::cpu_id();
    let mut node = MCSNode::new();
    let mut tasks = TASKS[cpu_id].lock(&mut node);

    while let Some(task) = tasks.pop() {
        task.wake();
    }
}

struct WorkerThreadContext {
    cpu_ctx: ArchContext,
    stack_mem: *mut u8,
    stack_mem_phy: usize,
    stack_size: usize,
}

impl WorkerThreadContext {
    fn new() -> Self {
        WorkerThreadContext {
            cpu_ctx: ArchContext::default(),
            stack_mem: null_mut(),
            stack_mem_phy: 0,
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

        let Some(stack_mem_phy) = memory::vm_to_phy(stack_mem as usize) else {
            return Err("failed to translate VM to Phy");
        };

        unsafe { memory::unmap(stack_mem as usize) };

        let mut cpu_ctx = ArchContext::default();

        unsafe {
            cpu_ctx.set_entry_point(entry, arg);
            cpu_ctx.set_stack_pointer(stack_pointer as usize);
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
        Ok(ptr) => {
            assert_eq!(ptr as usize & (PAGESIZE - 1), 0);
            Ok(ptr)
        }
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

pub fn get_pooled_thread() -> Option<PtrWorkerThreadContext> {
    let mut node = MCSNode::new();
    let mut threads = THREADS.lock(&mut node);

    threads.pooled.pop_front()
}

pub fn new_thread(
    entry: extern "C" fn(usize) -> !,
    arg: usize,
) -> Result<PtrWorkerThreadContext, &'static str> {
    PtrWorkerThreadContext::with_stack_and_entry(1024 * 1024 * 2, entry, arg)
}

pub fn deallocate_thread_pool() {
    let mut node = MCSNode::new();
    let mut threads = THREADS.lock(&mut node);

    while let Some(thread) = threads.pooled.pop_front() {
        unsafe { thread.delete() };
    }
}
