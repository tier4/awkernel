use crate::arch::ArchInterrupt;
use crate::heap;
use crate::sync::mutex::{MCSNode, Mutex};
use crate::unwind::catch_unwind;
use alloc::boxed::Box;
use alloc::collections::BTreeMap;

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
}

const MAX_IRQS: usize = 1024;

static INTERRUPT_CONTROLLER: Mutex<Option<Box<dyn InterruptController>>> = Mutex::new(None);
static IRQ_HANDLERS: Mutex<BTreeMap<usize, Box<dyn FnMut() + Send>>> = Mutex::new(BTreeMap::new());

pub fn register_interrupt_controller(controller: Box<dyn InterruptController>) {
    let mut node = MCSNode::new();
    let mut ctrl = INTERRUPT_CONTROLLER.lock(&mut node);
    *ctrl = Some(controller);
}

pub fn register_handler<F>(irq: usize, func: Box<F>) -> Result<(), ()>
where
    F: FnMut() + Send + 'static,
{
    if irq >= MAX_IRQS {
        return Err(());
    }

    let mut node = MCSNode::new();
    IRQ_HANDLERS.lock(&mut node).insert(irq, func);

    Ok(())
}

pub fn enable_irq(irq: usize) {
    let mut node = MCSNode::new();
    let mut controller = INTERRUPT_CONTROLLER.lock(&mut node);
    if let Some(ctrl) = controller.as_mut() {
        ctrl.enable_irq(irq);
    }
}

pub fn disable_irq(irq: usize) {
    let mut node = MCSNode::new();
    let mut controller = INTERRUPT_CONTROLLER.lock(&mut node);
    if let Some(ctrl) = controller.as_mut() {
        ctrl.disable_irq(irq);
    }
}

pub fn handle_irqs() {
    let mut node = MCSNode::new();
    let mut handlers = IRQ_HANDLERS.lock(&mut node);

    let mut node2 = MCSNode::new();
    let mut controller = INTERRUPT_CONTROLLER.lock(&mut node2);
    if let Some(ctrl) = controller.as_mut() {
        let iter = ctrl.pending_irqs();
        while let Some(irq) = iter.next() {
            if let Some(handler) = handlers.get_mut(&irq) {
                if let Err(err) = catch_unwind(|| {
                    let _guard = unsafe { heap::TALLOC.save() };
                    unsafe { heap::TALLOC.use_primary() };

                    handler();
                }) {
                    log::warn!("an interrupt handler has been panicked\n{err:?}");
                }
            }
        }
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
