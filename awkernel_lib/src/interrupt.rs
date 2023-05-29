use crate::arch::ArchInterrupt;
use crate::sync::mutex::{MCSNode, Mutex};
use alloc::boxed::Box;

pub trait Interrupt {
    fn get_flag() -> usize;
    fn disable();
    fn enable();
    fn set_flag(flag: usize);
}

pub trait InterruptController: Sync + Send {
    fn enable_irq(&mut self, irq: usize);
    fn disable_irq(&mut self, irq: usize);
    fn pending_irqs(&mut self) -> &mut dyn Iterator<Item=usize>;
}

type IrqHandler = fn();

const MAX_IRQS: usize = 64;
static INTERRUPT_CONTROLLER: Mutex<Option<Box<dyn InterruptController>>> = Mutex::new(None);
static IRQ_HANDLERS: Mutex<[Option<IrqHandler>; MAX_IRQS]> = Mutex::new([None; MAX_IRQS]);

pub fn register_interrupt_controller(controller: Box<dyn InterruptController>) {
    let mut node = MCSNode::new();
    INTERRUPT_CONTROLLER.lock(&mut node);
}

pub fn register_irq(irq: usize, func: IrqHandler) -> Result<(), ()> {
    let mut node = MCSNode::new();
    if irq >= MAX_IRQS || IRQ_HANDLERS.lock(&mut node)[irq].is_some() {
        return Err(());
    }

    IRQ_HANDLERS.lock(&mut node)[irq] = Some(func);
    Ok(())
}

pub fn enable_irq(irq: usize) {
    log::info!("enable_irq");
    let mut node = MCSNode::new();
    let mut controller = INTERRUPT_CONTROLLER.lock(&mut node);
    if let Some(ctrl) = controller.as_mut() {
        ctrl.enable_irq(irq);
    }
}

pub fn disable_irq(irq: usize) {
    log::info!("disable_irq");
    let mut node = MCSNode::new();
    let mut controller = INTERRUPT_CONTROLLER.lock(&mut node);
    if let Some(ctrl) = controller.as_mut() {
        ctrl.disable_irq(irq);
    }
}

pub fn handle_irqs() {
    log::info!("handle_irqs");
    let mut node = MCSNode::new();
    let handlers = IRQ_HANDLERS.lock(&mut node);
    let mut node2 = MCSNode::new();
    let mut controller = INTERRUPT_CONTROLLER.lock(&mut node2);
    if let Some(ctrl) = controller.as_mut() {
        let iter = ctrl.pending_irqs();
        while let Some(irq) = iter.next() {
            if let Some(handler) = handlers[irq] {
                handler();
            }
        }
    }
}

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