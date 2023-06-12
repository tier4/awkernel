use crate::{
    scheduler,
    task::{Task, TaskList},
};
use alloc::{
    boxed::Box,
    collections::{BTreeMap, VecDeque},
    sync::Arc,
};
use array_macro::array;
use awkernel_lib::{
    context::{context_switch, ArchContext, Context},
    cpu::NUM_MAX_CPU,
    interrupt::{self, InterruptGuard},
    memory::{self, Flags, PAGESIZE},
    sync::mutex::{MCSNode, Mutex},
    unwind::catch_unwind,
};
use core::{
    alloc::{GlobalAlloc, Layout},
    ptr::null_mut,
    sync::atomic::Ordering,
};
use futures::task::ArcWake;

/// Pooled and running threads.
static THREADS: Mutex<Threads> = Mutex::new(Threads::new());

/// Threads to be moved to THREADS::pooled.
static THREAD_POOL: [Mutex<VecDeque<PtrWorkerThreadContext>>; NUM_MAX_CPU] =
    array![_ => Mutex::new(VecDeque::new()); NUM_MAX_CPU];

/// Tasks to be rescheduled.
static RUNNABLE_TASKS: [Mutex<TaskList>; NUM_MAX_CPU] =
    array![_ => Mutex::new(TaskList::new()); NUM_MAX_CPU];

/// Tasks to be executed next.
static NEXT_TASK: [Mutex<TaskList>; NUM_MAX_CPU] =
    array![_ => Mutex::new(TaskList::new()); NUM_MAX_CPU];

struct Threads {
    pooled: VecDeque<PtrWorkerThreadContext>,
    running: BTreeMap<usize, PtrWorkerThreadContext>,
}

#[derive(Debug, Clone)]
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

    unsafe fn set_argument(&mut self, arg: usize) {
        let ptr = &mut *self.0;
        ptr.cpu_ctx.set_argument(arg);
    }
}

impl Threads {
    const fn new() -> Self {
        Threads {
            pooled: VecDeque::new(),
            running: BTreeMap::new(),
        }
    }
}

/// The current thread yields to `next` and it will be pooled.
pub unsafe fn yield_and_pool(next: PtrWorkerThreadContext) {
    let current_ctx = take_current_context();

    push_to_thread_pool(current_ctx.clone());

    unsafe {
        let current = &mut *(current_ctx.0);
        let next = &*next.0;

        context_switch(&mut current.cpu_ctx, &next.cpu_ctx);

        set_current_context(current_ctx);
    }

    re_schedule();
}

/// The thread of `current_task` yields to `next_thread`.
/// The current thread will be preempted, and waked soon.
fn yield_preempted_and_wake_task(next_thread: PtrWorkerThreadContext, current_task: Arc<Task>) {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    // Disable interrupt.
    let _int_guard = InterruptGuard::new();

    let current_ctx = take_current_context();

    {
        let mut node = MCSNode::new();
        let mut info = current_task.info.lock(&mut node);
        info.set_preempt_context(current_ctx.clone());
    }

    {
        let mut node = MCSNode::new();
        let mut tasks = RUNNABLE_TASKS[cpu_id].lock(&mut node);
        tasks.push(current_task.clone());
    }

    unsafe {
        // Save the current context.
        let current = &mut *(current_ctx.clone().0);
        let next = &*next_thread.0;

        context_switch(&mut current.cpu_ctx, &next.cpu_ctx);

        set_current_context(current_ctx);
    }

    re_schedule();
}

fn re_schedule() {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    {
        let mut node = MCSNode::new();
        let mut tasks = RUNNABLE_TASKS[cpu_id].lock(&mut node);

        while let Some(task) = tasks.pop() {
            task.wake();
        }
    }

    {
        let mut node = MCSNode::new();
        let mut pool = THREAD_POOL[cpu_id].lock(&mut node);

        let mut node = MCSNode::new();
        let mut threads = THREADS.lock(&mut node);

        while let Some(thread) = pool.pop_front() {
            threads.pooled.push_front(thread);
        }
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

/// Initialization for worker threads executed first.
pub fn init() {
    let ctx = PtrWorkerThreadContext::new();
    set_current_context(ctx);
}

fn take_current_context() -> PtrWorkerThreadContext {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    let mut node = MCSNode::new();
    let mut threads = THREADS.lock(&mut node);

    threads.running.remove(&cpu_id).unwrap()
}

fn set_current_context(ctx: PtrWorkerThreadContext) {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    let mut node = MCSNode::new();
    let mut threads = THREADS.lock(&mut node);

    assert!(threads.running.insert(cpu_id, ctx).is_none())
}

fn push_to_thread_pool(ctx: PtrWorkerThreadContext) {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    let mut node = MCSNode::new();
    let mut pool = THREAD_POOL[cpu_id].lock(&mut node);

    pool.push_back(ctx);
}

fn get_pooled_thread() -> Option<PtrWorkerThreadContext> {
    let mut node = MCSNode::new();
    let mut threads = THREADS.lock(&mut node);

    threads.pooled.pop_front()
}

fn new_thread(
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

unsafe fn do_preemption() {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    // If there is a running task on this CPU core, preemption is performed.
    // Otherwise, this function just returns.
    let task_id = super::RUNNING[cpu_id].load(Ordering::Relaxed);
    if task_id == 0 {
        return;
    }

    // If there is a task to be invoked next, execute the task.
    if let Some(next) = scheduler::get_next_task() {
        let current_task = {
            let mut node = MCSNode::new();
            let tasks = super::TASKS.lock(&mut node);
            let current_task = tasks.id_to_task.get(&task_id).unwrap();
            current_task.clone()
        };

        if let Some(next_thread) = {
            let mut node = MCSNode::new();
            let mut task_info = next.info.lock(&mut node);
            task_info.take_preempt_context()
        } {
            // If the next task is a preempted task, yield to it.
            yield_preempted_and_wake_task(next_thread, current_task);
        } else {
            // Otherwise, get a thread from the thread pool or create a new thread.

            let mut next_thread = if let Some(t) = get_pooled_thread() {
                // If there is a thread in the thread pool, use it,
                t
            } else if let Ok(t) = new_thread(thread_entry, 0) {
                // or create a new thread.
                t
            } else {
                next.wake();
                return;
            };

            next_thread.set_argument(next_thread.0 as usize);

            {
                // Insert the next task to the queue.
                let mut node = MCSNode::new();
                let mut next_task = NEXT_TASK[cpu_id].lock(&mut node);

                next_task.push(next);
            }

            yield_preempted_and_wake_task(next_thread, current_task);
        }
    }
}

#[no_mangle]
extern "C" fn thread_entry(arg: usize) -> ! {
    // Use only the primary heap memory region.

    #[cfg(not(feature = "std"))]
    unsafe {
        awkernel_lib::heap::TALLOC.use_primary()
    };

    let ctx = arg as *mut WorkerThreadContext;
    let ctx = PtrWorkerThreadContext(ctx);
    set_current_context(ctx);

    // Disable interrupt.
    interrupt::disable();

    // Re-schedule the preempted task.
    re_schedule();

    // Run the main function.
    super::run_main();

    awkernel_lib::delay::wait_forever();
}

pub unsafe fn preemption() {
    let _int_guard = InterruptGuard::new();

    #[cfg(not(feature = "std"))]
    let _heap_guard = {
        let heap_guard = awkernel_lib::heap::TALLOC.save();
        awkernel_lib::heap::TALLOC.use_primary();
        heap_guard
    };

    if let Err(e) = catch_unwind(|| do_preemption()) {
        #[cfg(not(feature = "std"))]
        awkernel_lib::heap::TALLOC.use_primary_then_backup();

        log::error!("caught panic!: {e:?}");
    }
}

pub fn get_next_task() -> Option<Arc<Task>> {
    let mut node = MCSNode::new();
    let mut next_task = NEXT_TASK[awkernel_lib::cpu::cpu_id()].lock(&mut node);
    next_task.pop()
}
