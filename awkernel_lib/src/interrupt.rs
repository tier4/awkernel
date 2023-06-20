use crate::{
    arch::ArchInterrupt,
    cpu::{self, NUM_MAX_CPU},
    sync::rwlock::RwLock,
    unwind::catch_unwind,
};
use alloc::{boxed::Box, collections::BTreeMap};
use array_macro::array;
use core::{
    mem::transmute,
    sync::atomic::{AtomicPtr, AtomicU16, AtomicUsize, Ordering},
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
    fn enable_irq(&mut self, irq: u16);
    fn disable_irq(&mut self, irq: u16);
    fn pending_irqs<'a>(&self) -> Box<dyn Iterator<Item = u16>>;

    /// Send an inter-process interrupt to `target` CPU.
    fn send_ipi(&mut self, irq: u16, target: u16);

    /// Send an inter-process interrupt to all CPUs.
    fn send_ipi_broadcast(&mut self, irq: u16);

    /// Send an inter-process interrupt to all CPUs except the sender CPU.
    fn send_ipi_broadcast_without_self(&mut self, irq: u16);

    /// Initialization for non-primary core.
    fn init_non_primary(&mut self) {}
}

const MAX_IRQS: u16 = 1024;

static INTERRUPT_CONTROLLER: RwLock<Option<Box<dyn InterruptController>>> = RwLock::new(None);
static IRQ_HANDLERS: RwLock<BTreeMap<u16, Box<dyn Fn() + Send>>> = RwLock::new(BTreeMap::new());

static PREEMPT_IRQ: AtomicU16 = AtomicU16::new(!0);
static PREEMPT_FN: AtomicPtr<()> = AtomicPtr::new(empty as *mut ());

static NUM_INTERRUPT: [AtomicUsize; NUM_MAX_CPU] = array![_ => AtomicUsize::new(0); NUM_MAX_CPU];

fn empty() {}

pub fn register_interrupt_controller(controller: Box<dyn InterruptController>) {
    let mut ctrl = INTERRUPT_CONTROLLER.write();
    *ctrl = Some(controller);
}

pub fn register_handler<F>(irq: u16, func: Box<F>) -> Result<(), &'static str>
where
    F: Fn() + Send + 'static,
{
    if irq >= MAX_IRQS {
        return Err("The IRQ# is greater than MAX_IRQS.");
    }

    IRQ_HANDLERS.write().insert(irq, func);

    Ok(())
}

pub fn enable_irq(irq: u16) {
    let mut controller = INTERRUPT_CONTROLLER.write();
    if let Some(ctrl) = controller.as_mut() {
        ctrl.enable_irq(irq);
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
    }
}

pub fn disable_irq(irq: u16) {
    let mut controller = INTERRUPT_CONTROLLER.write();
    if let Some(ctrl) = controller.as_mut() {
        ctrl.disable_irq(irq);
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
    }
}

/// Send an inter-process interrupt to `target` CPU.
pub fn send_ipi(irq: u16, target: u16) {
    let mut controller = INTERRUPT_CONTROLLER.write();
    if let Some(ctrl) = controller.as_mut() {
        ctrl.send_ipi(irq, target);
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
    }
}

/// Send an inter-process interrupt to all CPUs.
pub fn send_ipi_broadcast(irq: u16) {
    let mut controller = INTERRUPT_CONTROLLER.write();
    if let Some(ctrl) = controller.as_mut() {
        ctrl.send_ipi_broadcast(irq);
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
    }
}

/// Send an inter-process interrupt to all CPUs except the sender CPU.
pub fn send_ipi_broadcast_without_self(irq: u16) {
    let mut controller = INTERRUPT_CONTROLLER.write();
    if let Some(ctrl) = controller.as_mut() {
        ctrl.send_ipi_broadcast_without_self(irq);
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
    }
}

pub fn handle_irqs() {
    let cpu_id = cpu::cpu_id();
    NUM_INTERRUPT[cpu_id].fetch_add(1, Ordering::Relaxed);

    let handlers = IRQ_HANDLERS.read();
    let mut need_preemption = false;

    let controller = INTERRUPT_CONTROLLER.read();
    if let Some(ctrl) = controller.as_ref() {
        let iter = ctrl.pending_irqs();
        drop(controller); // unlock

        // Use the primary allocator.
        let _guard = {
            let g = heap::TALLOC.save();
            unsafe { heap::TALLOC.use_primary() };
            g
        };

        for irq in iter {
            if irq == PREEMPT_IRQ.load(Ordering::Relaxed) {
                need_preemption = true;
            }

            if let Some(handler) = handlers.get(&irq) {
                if let Err(err) = catch_unwind(|| {
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
    let mut controller = INTERRUPT_CONTROLLER.write();
    if let Some(ctrl) = controller.as_mut() {
        ctrl.init_non_primary();
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
    }
}

/// When the interrupt request of `irq` is received,
/// `preemption` will be called.
pub fn set_preempt_irq(irq: u16, preemption: unsafe fn()) {
    PREEMPT_IRQ.store(irq, Ordering::Relaxed);
    PREEMPT_FN.store(preemption as *mut (), Ordering::Relaxed);
}
