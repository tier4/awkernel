use crate::arch::ArchImpl;
use alloc::{
    borrow::Cow,
    collections::{btree_map::Entry, BTreeMap},
};
use core::sync::atomic::{AtomicPtr, AtomicU16, Ordering};

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;

#[cfg(feature = "x86")]
use crate::arch::x86_64::interrupt_remap;

#[cfg(loom)]
use crate::sync::rwlock_dummy::RwLock;

#[cfg(not(loom))]
use crate::sync::rwlock::RwLock;

pub trait Interrupt {
    fn get_flag() -> usize;
    fn disable();
    fn enable();
    fn set_flag(flag: usize);
}

pub trait InterruptController: Sync + Send {
    fn enable_irq(&mut self, irq: u16);
    fn disable_irq(&mut self, irq: u16);
    fn pending_irqs(&self) -> Box<dyn Iterator<Item = u16>>;

    /// Send an inter-process interrupt to `target` CPU.
    fn send_ipi(&mut self, irq: u16, target: u32);

    /// Send an inter-process interrupt to all CPUs.
    fn send_ipi_broadcast(&mut self, irq: u16);

    /// Send an inter-process interrupt to all CPUs except the sender CPU.
    fn send_ipi_broadcast_without_self(&mut self, irq: u16);

    /// Initialization for non-primary core.
    fn init_non_primary(&mut self) {}

    /// End of interrupt.
    /// This will be used by only x86_64.
    fn eoi(&mut self) {}

    /// Return the range of IRQs, which can be registered.
    /// The range is [start, end).
    fn irq_range(&self) -> (u16, u16);

    /// Return the range of IRQs, which can be used for PnP devices.
    /// The range is [start, end).
    fn irq_range_for_pnp(&self) -> (u16, u16);

    /// Set the PCIe MSI or MSI-X interrupt
    #[allow(unused_variables)]
    fn set_pcie_msi(
        &self,
        segment_number: usize,
        target: u32,
        irq: u16,
        message_data: &mut u32,
        message_address: &mut u32,
        message_address_upper: Option<&mut u32>,
    ) -> Result<IRQ, &'static str> {
        Err("Interrupt controller does not support PCIe MSI or MSI-X.")
    }
}

type NameAndCallback = (Cow<'static, str>, Box<dyn Fn(u16) + Send>);

static INTERRUPT_CONTROLLER: RwLock<Option<Box<dyn InterruptController>>> = RwLock::new(None);
static IRQ_HANDLERS: RwLock<BTreeMap<u16, NameAndCallback>> = RwLock::new(BTreeMap::new());

static PREEMPT_IRQ: AtomicU16 = AtomicU16::new(!0);
static PREEMPT_FN: AtomicPtr<()> = AtomicPtr::new(empty as *mut ());

fn empty() {}

/// Return the list of IRQs and their handlers.
pub fn get_handlers() -> BTreeMap<u16, Cow<'static, str>> {
    let handlers = IRQ_HANDLERS.read();
    let mut map = BTreeMap::new();

    for (irq, (name, _)) in handlers.iter() {
        map.insert(*irq, name.clone());
    }

    map.insert(PREEMPT_IRQ.load(Ordering::Relaxed), "preemption".into());

    map
}

/// Register an interrupt controller.
///
/// # Safety
///
/// This function is unsafe because the caller must ensure that the interrupt controller is valid.
/// The interrupt controller should be initialized only once.
pub unsafe fn register_interrupt_controller(controller: Box<dyn InterruptController>) {
    let mut ctrl = INTERRUPT_CONTROLLER.write();
    *ctrl = Some(controller);
}

#[derive(Debug)]
pub enum IRQ {
    Basic(u16),

    #[cfg(feature = "x86")]
    X86InterruptRemap {
        irq: u16,
        remap_info: interrupt_remap::RemapInfo,
    },
}

impl IRQ {
    pub fn get_irq(&self) -> u16 {
        match self {
            IRQ::Basic(irq) => *irq,

            #[cfg(feature = "x86")]
            IRQ::X86InterruptRemap { irq, .. } => *irq,
        }
    }

    pub fn enable(&mut self) {
        match self {
            IRQ::Basic(irq) => enable_irq(*irq),

            #[cfg(feature = "x86")]
            IRQ::X86InterruptRemap { irq, .. } => enable_irq(*irq),
        }
    }

    pub fn disable(&mut self) {
        match self {
            IRQ::Basic(irq) => disable_irq(*irq),

            #[cfg(feature = "x86")]
            IRQ::X86InterruptRemap { irq, .. } => disable_irq(*irq),
        }
    }
}

impl Drop for IRQ {
    fn drop(&mut self) {
        self.disable();

        let mut handlers = IRQ_HANDLERS.write();

        match self {
            IRQ::Basic(irq) => {
                handlers.remove(irq);
            }

            #[cfg(feature = "x86")]
            IRQ::X86InterruptRemap { irq, .. } => {
                handlers.remove(irq);
            }
        }
    }
}

/// Register an interrupt handler.
/// If the handler is already registered, this function will return an error.
pub fn register_handler<F>(
    irq: u16,
    name: Cow<'static, str>,
    func: Box<F>,
) -> Result<(), &'static str>
where
    F: Fn(u16) + Send + 'static,
{
    let controller = INTERRUPT_CONTROLLER.read();
    let (min, max) = if let Some(ctrl) = controller.as_ref() {
        ctrl.irq_range()
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
        return Err("Interrupt controller is not yet enabled.");
    };

    if min <= irq && irq < max {
        let mut handlers = IRQ_HANDLERS.write();
        let entry = handlers.entry(irq);

        match entry {
            Entry::Occupied(_) => {
                log::warn!("IRQ #{irq} is already registered.");
                return Err("IRQ is already registered.");
            }
            Entry::Vacant(ve) => {
                ve.insert((name, func));
            }
        }

        Ok(())
    } else {
        log::warn!("IRQ #{irq} is out of range.");
        Err("IRQ is out of range.")
    }
}

/// Enable the interrupt.
pub fn enable_irq(irq: u16) {
    let mut controller = INTERRUPT_CONTROLLER.write();
    if let Some(ctrl) = controller.as_mut() {
        ctrl.enable_irq(irq);
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
    }
}

/// Disable the interrupt.
pub fn disable_irq(irq: u16) {
    let mut controller = INTERRUPT_CONTROLLER.write();
    if let Some(ctrl) = controller.as_mut() {
        ctrl.disable_irq(irq);
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
    }
}

/// Send an inter-process interrupt to `target` CPU.
pub fn send_ipi(irq: u16, target: u32) {
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

/// Register an interrupt handler for PCIe MSI or MSI-X  interrupt.
/// This returns an IRQ object, which can be used to enable or disable the interrupt.
/// When dropping the IRQ object, the interrupt will be disabled and the handler will be removed.
pub fn register_handler_pcie_msi<F>(
    name: Cow<'static, str>,
    func: Box<F>,
    segment_number: usize,
    target: u32,
    message_data: &mut u32,
    message_address: &mut u32,
    message_address_upper: Option<&mut u32>,
) -> Result<IRQ, &'static str>
where
    F: Fn(u16) + Send + 'static,
{
    let mut controller = INTERRUPT_CONTROLLER.write();

    let (min, max) = if let Some(ctrl) = controller.as_ref() {
        ctrl.irq_range()
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
        return Err("Interrupt controller is not yet enabled.");
    };

    let mut handlers = IRQ_HANDLERS.write();
    let mut irq = None;
    for i in min..max {
        let entry = handlers.entry(i);

        if let Entry::Vacant(ve) = entry {
            ve.insert((name, func));
            irq = Some(i);
            break;
        }
    }

    let irq = irq.ok_or("There is no vacant IRQ.")?;

    let Some(ctrl) = controller.as_mut() else {
        log::warn!("Interrupt controller is not yet enabled.");
        return Err("Interrupt controller is not yet enabled.");
    };

    let result = ctrl.set_pcie_msi(
        segment_number,
        target,
        irq,
        message_data,
        message_address,
        message_address_upper,
    );

    if result.is_err() {
        handlers.remove(&irq);
    }

    result
}

/// Handle the pending interrupt request.
/// This function will be used by only x86_64 and called from CPU's interrupt handlers.
#[cfg(feature = "x86")]
pub fn handle_irq(irq: u16) {
    use crate::{heap, unwind::catch_unwind};

    let handlers = IRQ_HANDLERS.read();
    if let Some((name, handler)) = handlers.get(&irq) {
        // Use the primary allocator.
        #[cfg(not(feature = "std"))]
        let _guard = {
            let g = heap::TALLOC.save();
            unsafe { heap::TALLOC.use_primary() };
            g
        };

        let f = || {
            handler(irq);
        };

        if catch_unwind(f).is_err() {
            log::warn!("an interrupt handler has been panicked: name = {name}, irq = {irq}");
        }
    }
}

/// Handle all pending interrupt requests.
/// This function will be used by only aarch64 and called from CPU's interrupt handlers.
#[cfg(feature = "aarch64")]
pub fn handle_irqs() {
    use crate::{heap, unwind::catch_unwind};
    use core::mem::transmute;

    let handlers = IRQ_HANDLERS.read();
    let mut need_preemption = false;

    let controller = INTERRUPT_CONTROLLER.read();
    if let Some(ctrl) = controller.as_ref() {
        let iter = ctrl.pending_irqs();
        drop(controller); // unlock

        // Use the primary allocator.
        #[cfg(not(feature = "std"))]
        let _guard = {
            let g = heap::TALLOC.save();
            unsafe { heap::TALLOC.use_primary() };
            g
        };

        for irq in iter {
            if irq == PREEMPT_IRQ.load(Ordering::Relaxed) {
                need_preemption = true;
                continue;
            }

            if let Some((_, handler)) = handlers.get(&irq) {
                if let Err(err) = catch_unwind(|| {
                    handler(irq);
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

/// Handle preemption.
#[cfg(feature = "x86")]
pub fn handle_preemption() {
    use core::mem::transmute;

    let ptr = PREEMPT_FN.load(Ordering::Relaxed);
    let preemption = unsafe { transmute::<*mut (), fn()>(ptr) };
    preemption();
}

/// Disable interrupts and automatically restored the configuration.
///
/// ```
/// {
///     use awkernel_lib::interrupt::InterruptGuard;
///
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
        let flag = ArchImpl::get_flag();
        ArchImpl::disable();

        Self { flag }
    }
}

impl Drop for InterruptGuard {
    fn drop(&mut self) {
        ArchImpl::set_flag(self.flag);
    }
}

/// Enable interrupts.
pub fn enable() {
    ArchImpl::enable();
}

/// Disable interrupts.
pub fn disable() {
    ArchImpl::disable();
}

/// Initialization for non-primary core.
pub unsafe fn init_non_primary() {
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

/// Return the IRQ number for preemption.
pub fn get_preempt_irq() -> u16 {
    PREEMPT_IRQ.load(Ordering::Relaxed)
}

/// Check the initialization status of the interrupt module.
pub fn sanity_check() {
    if INTERRUPT_CONTROLLER.read().is_none() {
        log::warn!("interrupt::INTERRUPT_CONTROLLER is not yet initialized.")
    } else {
        log::info!("interrupt::INTERRUPT_CONTROLLER has been initialized.");
    }

    if PREEMPT_FN.load(Ordering::Relaxed) == empty as *mut () {
        log::warn!("interrupt::PREEMPT_FN is not yet initialized.")
    } else {
        log::info!("interrupt::PREEMPT_FN has been initialized.")
    }
}

/// End of interrupt.
/// This function will be used by only x86_64.
pub fn eoi() {
    let mut controller = INTERRUPT_CONTROLLER.write();
    if let Some(ctrl) = controller.as_mut() {
        ctrl.eoi();
    } else {
        log::warn!("Interrupt controller is not yet enabled.");
    }
}
