use crate::{
    delay::wait_microsec,
    scheduler::{self, get_scheduler, Scheduler, SchedulerType},
};
use alloc::{borrow::Cow, boxed::Box, collections::BTreeMap, sync::Arc};
use core::{
    ptr::{read_volatile, write_volatile},
    task::{Context, Poll},
};
use futures::{
    future::BoxFuture,
    task::{waker_ref, ArcWake},
    Future,
};
use synctools::mcs::{MCSLock, MCSNode};

pub type TaskResult = Result<(), Cow<'static, str>>;

static TASKS: MCSLock<Tasks> = MCSLock::new(Tasks::new());
static mut RUNNING: [Option<u64>; 512] = [None; 512];

pub struct Task {
    id: u64,
    future: MCSLock<BoxFuture<'static, TaskResult>>,
    scheduler: &'static dyn Scheduler,
}

unsafe impl Sync for Task {}
unsafe impl Send for Task {}

impl ArcWake for Task {
    fn wake_by_ref(arc_self: &Arc<Self>) {
        let cloned = arc_self.clone();
        cloned.wake();
    }

    fn wake(self: Arc<Self>) {
        self.scheduler.wake_task(self);
    }
}

impl Task {
    pub fn get_id(&self) -> u64 {
        self.id
    }
}

#[derive(Default)]
struct Tasks {
    candidate_id: u64,
    id_to_task: BTreeMap<u64, Arc<Task>>,
}

impl Tasks {
    const fn new() -> Self {
        Self {
            candidate_id: 0,
            id_to_task: BTreeMap::new(),
        }
    }

    fn spawn(
        &mut self,
        future: BoxFuture<'static, TaskResult>,
        scheduler: &'static dyn Scheduler,
    ) -> u64 {
        let mut id = self.candidate_id;
        loop {
            if self.id_to_task.contains_key(&id) {
                id += 1;
            } else {
                let task = Task {
                    future: MCSLock::new(future),
                    scheduler,
                    id,
                };
                self.id_to_task.insert(id, Arc::new(task));
                self.candidate_id += 1;
                return id;
            }
        }
    }

    fn wake(&self, id: u64) {
        if let Some(task) = self.id_to_task.get(&id) {
            task.clone().wake();
        }
    }

    fn remove(&mut self, id: u64) {
        self.id_to_task.remove(&id);
    }
}

pub fn spawn(
    future: impl Future<Output = TaskResult> + 'static + Send,
    sched_type: SchedulerType,
) -> u64 {
    let future = Box::pin(future);

    let scheduler = match sched_type {
        SchedulerType::RoundRobin => get_scheduler(sched_type),
    };

    let mut node = MCSNode::new();
    let mut tasks = TASKS.lock(&mut node);
    let id = tasks.spawn(future, scheduler);
    tasks.wake(id);

    id
}

pub fn get_current_task(cpu_id: usize) -> Option<u64> {
    unsafe { read_volatile(&RUNNING[cpu_id]) }
}

pub fn run(cpu_id: usize) {
    loop {
        if let Some(task) = scheduler::get_next_task() {
            let w = waker_ref(&task);
            let mut ctx = Context::from_waker(&w);

            let mut node = MCSNode::new();
            let mut guard = task.future.lock(&mut node);

            unsafe { write_volatile(&mut RUNNING[cpu_id], Some(task.id)) };

            match unwinding::panic::catch_unwind(|| guard.as_mut().poll(&mut ctx)) {
                Ok(Poll::Pending) => (),
                Ok(Poll::Ready(result)) => {
                    if let Err(msg) = result {
                        log::error!("A task has failed: {msg}");
                    }

                    let mut node = MCSNode::new();
                    let mut tasks = TASKS.lock(&mut node);
                    tasks.remove(task.id);
                }
                Err(err) => {
                    log::error!("A task has panicked!: {:?}", err);
                }
            }
        } else {
            wait_microsec(1);
        }
    }
}
