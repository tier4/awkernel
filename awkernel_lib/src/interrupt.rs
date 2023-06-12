use crate::{
    arch::ArchInterrupt,
    sync::{
        mutex::{MCSNode, Mutex},
        rwlock::RwLock,
    },
    unwind::catch_unwind,
};
use alloc::{boxed::Box, collections::BTreeMap};
use core::{
    mem::transmute,
    sync::atomic::{AtomicPtr, AtomicUsize, Ordering},
};

#[cfg(not(feature = "std"))]
use crate::heap;

pub trait Interrupt {
    fn get_flag() -> usize;
    fn disable();
    fn enable();
    fn set_flag(flag: usize);
}

pub trait InterruptController: Sync + Send {
    fn enable_irq(&mut self, irq: usize);
    fn disable_irq(&mut self, irq: usize);
    fn pending_irqs(&mut self) -> &mut dyn Iterator<Item = usize>;

    /// Send an inter-process interrupt to `target` CPU.
    fn send_ipi(&mut self, target: usize);

    /// Send an inter-process interrupt to every CPU.
    fn send_ipi_broadcast(&mut self);

    /// Send an inter-process interrupt to every CPU except the sender CPU.
    fn send_ipi_broadcast_without_self(&mut self);

    /// Initialization for non-primary core.
    fn init_non_primary(&mut self) {}
}

const MAX_IRQS: usize = 1024;

static INTERRUPT_CONTROLLER: Mutex<Option<Box<dyn InterruptController>>> = Mutex::new(None);
static IRQ_HANDLERS: RwLock<BTreeMap<usize, Box<dyn Fn() + Send>>> = RwLock::new(BTreeMap::new());

static PREEMPT_IRQ: AtomicUsize = AtomicUsize::new(!0);
static PREEMPT_FN: AtomicPtr<()> = AtomicPtr::new(empty as *mut ());

fn empty() {}

pub fn register_interrupt_controller(controller: Box<dyn InterruptController>) {
    let mut node = MCSNode::new();
    let mut ctrl = INTERRUPT_CONTROLLER.lock(&mut node);
    *ctrl = Some(controller);
}

pub fn register_handler<F>(irq: usize, func: Box<F>) -> Result<(), &'static str>
where
    F: Fn() + Send + 'static,
{
    if irq >= MAX_IRQS {
        return Err("The IRQ# is greater than MAX_IRQS.");
    }

    IRQ_HANDLERS.write().insert(irq, func);

    Ok(())
}

pub fn enable_irq(irq: usize) {
    let mut node = MCSNode::new();
    let mut controller = INTERRUPT_CONTROLLER.lock(&mut node);
    if let Some(ctrl) = controller.as_mut() {
        ctrl.enable_irq(irq);
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
    }
}

pub fn disable_irq(irq: usize) {
    let mut node = MCSNode::new();
    let mut controller = INTERRUPT_CONTROLLER.lock(&mut node);
    if let Some(ctrl) = controller.as_mut() {
        ctrl.disable_irq(irq);
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
    }
}

pub fn handle_irqs() {
    let handlers = IRQ_HANDLERS.read();
    let mut need_preemption = false;

    let mut node2 = MCSNode::new();
    let mut controller = INTERRUPT_CONTROLLER.lock(&mut node2);
    if let Some(ctrl) = controller.as_mut() {
        let iter = ctrl.pending_irqs();
        while let Some(irq) = iter.next() {
            if irq == PREEMPT_IRQ.load(Ordering::Relaxed) {
                need_preemption = true;
            }

            if let Some(handler) = handlers.get(&irq) {
                if let Err(err) = catch_unwind(|| {
                    // Use the primary allocator.
                    #[cfg(not(feature = "std"))]
                    let _guard = heap::TALLOC.save();

                    #[cfg(not(feature = "std"))]
                    unsafe {
                        heap::TALLOC.use_primary()
                    };

                    handler();
                }) {
                    log::warn!("an interrupt handler has been panicked\n{err:?}");
                }
            }
        }
    }

    if need_preemption {
        let ptr = PREEMPT_FN.load(Ordering::Relaxed);
        let preemption = unsafe { transmute::<*mut (), fn()>(ptr) };
        preemption();
    }
}

/// Disable interrupts and automatically restored the configuration.
///
/// ```
/// {
///     let _int_guard = InterruptGuard::new();
///     // interrupts are disabled.
/// }
/// // The configuration will be restored here.
/// ```
pub struct InterruptGuard {
    flag: usize,
}

impl Default for InterruptGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl InterruptGuard {
    pub fn new() -> Self {
        let flag = ArchInterrupt::get_flag();
        ArchInterrupt::disable();

        Self { flag }
    }
}

impl Drop for InterruptGuard {
    fn drop(&mut self) {
        ArchInterrupt::set_flag(self.flag);
    }
}

pub fn enable() {
    ArchInterrupt::enable();
}

pub fn disable() {
    ArchInterrupt::disable();
}

/// Initialization for non-primary core.
pub fn init_non_primary() {
    let mut node = MCSNode::new();
    let mut controller = INTERRUPT_CONTROLLER.lock(&mut node);
    if let Some(ctrl) = controller.as_mut() {
        ctrl.init_non_primary();
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
    }
}

/// When the interrupt request of `irq` is received,
/// `preemption` will be called.
pub fn set_preempt_irq(irq: usize, preemption: unsafe fn()) {
    PREEMPT_IRQ.store(irq, Ordering::Relaxed);
    PREEMPT_FN.store(preemption as *mut (), Ordering::Relaxed);
}
