use crate::task::{get_current_task, Task, IN_TRANSITION};
use alloc::{collections::VecDeque, sync::Arc};
use array_macro::array;
use awkernel_lib::{
    context::context_switch,
    cpu::NUM_MAX_CPU,
    interrupt::{self, InterruptGuard},
    sync::mutex::{MCSNode, Mutex},
    unwind::catch_unwind,
};
use core::sync::atomic::{AtomicUsize, Ordering};
use thread::PtrWorkerThreadContext;

#[cfg(feature = "perf")]
use crate::task::{
    cpu_counter,
    perf::{add_context_restore_start, add_context_save_end, ContextSwitchType},
};

pub mod thread;

/// Threads to be moved to THREADS::pooled.
static THREAD_POOL: [Mutex<VecDeque<PtrWorkerThreadContext>>; NUM_MAX_CPU] =
    array![_ => Mutex::new(VecDeque::new()); NUM_MAX_CPU];

/// Tasks to be rescheduled.
static PREEMPTED_TASKS: [Mutex<VecDeque<Arc<Task>>>; NUM_MAX_CPU] =
    array![_ => Mutex::new(VecDeque::new()); NUM_MAX_CPU];

/// Tasks to be executed next.
static NEXT_TASK: [Mutex<VecDeque<Arc<Task>>>; NUM_MAX_CPU] =
    array![_ => Mutex::new(VecDeque::new()); NUM_MAX_CPU];

static NUM_PREEMPTION: AtomicUsize = AtomicUsize::new(0);

/// The current thread yields to `next_ctx`, and the current thread will be pooled.
pub unsafe fn yield_and_pool(next_ctx: PtrWorkerThreadContext) {
    let mut current_ctx = thread::take_current_context();

    push_to_thread_pool(current_ctx.clone());

    let current_cpu_ctx = current_ctx.get_cpu_context_mut();
    let next_cpu_ctx = next_ctx.get_cpu_context();

    #[cfg(feature = "perf")]
    add_context_save_end(
        ContextSwitchType::Yield,
        awkernel_lib::cpu::cpu_id(),
        cpu_counter(),
    );

    unsafe { context_switch(current_cpu_ctx, next_cpu_ctx) };

    #[cfg(feature = "perf")]
    add_context_restore_start(
        ContextSwitchType::Yield,
        awkernel_lib::cpu::cpu_id(),
        cpu_counter(),
    );

    thread::set_current_context(current_ctx);

    re_schedule();
}

/// The thread of `current_task` yields to `next_thread`.
/// The current thread will be preempted, and waked soon.
fn yield_preempted_and_wake_task(current_task: Arc<Task>, next_thread: PtrWorkerThreadContext) {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    let mut current_ctx = thread::take_current_context();

    {
        let mut node = MCSNode::new();
        let mut info = current_task.info.lock(&mut node);
        info.set_preempt_context(current_ctx.clone());
        info.state = super::State::Preempted;
        info.num_preempt += 1;
    }

    {
        let mut node = MCSNode::new();
        let mut tasks = PREEMPTED_TASKS[cpu_id].lock(&mut node);
        tasks.push_front(current_task);
    }

    NUM_PREEMPTION.fetch_add(1, Ordering::Relaxed);

    let current_cpu_ctx = current_ctx.get_cpu_context_mut();
    let next_cpu_ctx = next_thread.get_cpu_context();

    unsafe {
        #[cfg(feature = "perf")]
        add_context_save_end(ContextSwitchType::Preempt, cpu_id, cpu_counter());

        // Save the current context.
        context_switch(current_cpu_ctx, next_cpu_ctx);

        #[cfg(feature = "perf")]
        add_context_restore_start(
            ContextSwitchType::Preempt,
            awkernel_lib::cpu::cpu_id(),
            cpu_counter(),
        );
        thread::set_current_context(current_ctx);
    }

    re_schedule();
}

fn re_schedule() {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    {
        let mut node = MCSNode::new();
        let mut tasks = PREEMPTED_TASKS[cpu_id].lock(&mut node);

        while let Some(task) = tasks.pop_front() {
            task.scheduler.wake_task(task);
        }
    }

    {
        let mut node = MCSNode::new();
        let mut pool = THREAD_POOL[cpu_id].lock(&mut node);

        while let Some(thread) = pool.pop_front() {
            thread::make_thread_pooled(thread);
        }
    }
}

/// Initialization for worker threads executed first.
pub fn init() {
    let ctx = PtrWorkerThreadContext::new();
    thread::set_current_context(ctx);
}

fn push_to_thread_pool(ctx: PtrWorkerThreadContext) {
    let cpu_id = awkernel_lib::cpu::cpu_id();

    let mut node = MCSNode::new();
    let mut pool = THREAD_POOL[cpu_id].lock(&mut node);

    pool.push_back(ctx);
}

/// Take the current task ID from, `super::RUNNING[cpu_id]`, and assign 0 to there.
/// `super::RUNNING[cpu_id]` will be restored after dropping.
struct RunningTaskGuard(u32);

impl RunningTaskGuard {
    fn take() -> Option<Self> {
        let cpu_id = awkernel_lib::cpu::cpu_id();
        let task_id = super::RUNNING[cpu_id].swap(0, Ordering::Relaxed);
        if task_id != 0 {
            Some(Self(task_id))
        } else {
            None
        }
    }
}

impl Drop for RunningTaskGuard {
    fn drop(&mut self) {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        let mut node = MCSNode::new();
        let tasks = super::TASKS.lock(&mut node);
        let task = tasks.id_to_task.get(&self.0).unwrap();

        {
            let mut node = MCSNode::new();
            let mut info = task.info.lock(&mut node);
            info.update_last_executed();
        }

        super::RUNNING[cpu_id].store(self.0, Ordering::Relaxed);
        IN_TRANSITION[cpu_id].store(false, Ordering::Relaxed);
    }
}

unsafe fn do_preemption() {
    // If there is a running task on this CPU core, preemption will be performed.
    // Otherwise, this function just returns.
    let Some(task_id) = RunningTaskGuard::take() else {
        return;
    };

    {
        let mut node = MCSNode::new();
        let tasks = super::TASKS.lock(&mut node);
        let task = tasks.id_to_task.get(&task_id.0).unwrap();

        let mut node = MCSNode::new();
        let mut info = task.info.lock(&mut node);
        if !info.need_preemption {
            return;
        } else {
            info.need_preemption = false;
        }
    }

    // If there is a task to be invoked next, execute the task.
    if let Some(next) = super::get_next_task() {
        let current_task = {
            let mut node = MCSNode::new();
            let tasks = super::TASKS.lock(&mut node);
            let current_task = tasks.id_to_task.get(&task_id.0).unwrap();
            current_task.clone()
        };

        if let Some(next_thread) = {
            let mut node = MCSNode::new();
            let mut task_info = next.info.lock(&mut node);
            task_info.take_preempt_context()
        } {
            // If the next task is a preempted task, yield to it.
            yield_preempted_and_wake_task(current_task, next_thread);
        } else {
            // Otherwise, get a thread from the thread pool or create a new thread.

            let next_thread = if let Some(t) = thread::take_pooled_thread() {
                // If there is a thread in the thread pool, use it,
                t
            } else if let Ok(mut t) = thread::create_thread(thread_entry, 0) {
                // or create a new thread.

                // Set an argument.
                unsafe { t.set_argument(t.get_cpu_context() as *const _ as usize) };

                t
            } else {
                // failed to create thread.
                log::warn!("failed to create a worker thread.");
                next.scheduler.wake_task(next);
                return;
            };

            {
                let cpu_id = awkernel_lib::cpu::cpu_id();

                // Insert the next task to the queue.
                let mut node = MCSNode::new();
                let mut next_task = NEXT_TASK[cpu_id].lock(&mut node);

                next_task.push_back(next);
            }

            yield_preempted_and_wake_task(current_task, next_thread);
        }
    }
}

extern "C" fn thread_entry(arg: usize) -> ! {
    // Use only the primary heap memory region.

    #[cfg(not(feature = "std"))]
    unsafe {
        awkernel_lib::heap::TALLOC.use_primary()
    };

    let ctx = unsafe { PtrWorkerThreadContext::with_context(arg) };
    thread::set_current_context(ctx);

    // Disable interrupt.
    interrupt::disable();

    // Re-schedule the preempted task.
    re_schedule();

    let cpu_id = awkernel_lib::cpu::cpu_id();
    assert_eq!(None, get_current_task(cpu_id));

    // Run the main function.
    super::run_main();

    awkernel_lib::delay::wait_forever();
}

/// Preempt to the next executable task.
///
/// # Safety
///
/// Do not call this function during mutex locking.
pub unsafe fn preemption() {
    let _int_guard = InterruptGuard::new();

    let _heap_guard = {
        let heap_guard = awkernel_lib::heap::TALLOC.save();
        awkernel_lib::heap::TALLOC.use_primary();
        heap_guard
    };

    if let Err(e) = catch_unwind(|| do_preemption()) {
        awkernel_lib::heap::TALLOC.use_primary_then_backup();
        log::error!("caught panic!: {e:?}");
    }
}

pub fn get_next_task() -> Option<Arc<Task>> {
    let mut node = MCSNode::new();
    let mut next_task = NEXT_TASK[awkernel_lib::cpu::cpu_id()].lock(&mut node);
    next_task.pop_front()
}

pub fn get_num_preemption() -> usize {
    NUM_PREEMPTION.load(Ordering::Relaxed)
}
