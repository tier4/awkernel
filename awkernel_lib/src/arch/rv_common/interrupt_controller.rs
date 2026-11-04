use super::{clint::Clint, plic::Plic};
use crate::{
    cpu::{cpu_id, num_cpu},
    interrupt,
};
use alloc::boxed::Box;
use core::sync::atomic::{AtomicU8, Ordering};

// TODO: get info from device tree
static INTERRUPT_CONTROLLER: InterruptController = InterruptController::qemu_virt();

pub struct InterruptController {
    clint: Clint,
    plic: Plic,
}

impl InterruptController {
    /// CLINT and PLIC layout of the QEMU `virt` machine.
    const fn qemu_virt() -> Self {
        Self {
            clint: Clint {
                base_addr: 0x0200_0000,
                mtime_freq: 10_000_000,
            },
            plic: Plic {
                base_addr: 0x0c00_0000,
                max_priority: 7,
                num_sources: 53,
                num_contexts: 16,
            },
        }
    }
}

#[inline]
pub(super) const fn clint() -> &'static Clint {
    &INTERRUPT_CONTROLLER.clint
}

/// PLIC context of the current hart in M-mode.
///
/// Each hart has two PLIC contexts: `2 * hart_id` for M-mode and
/// `2 * hart_id + 1` for S-mode. Awkernel currently runs in M-mode.
#[inline]
fn plic_context() -> u16 {
    (cpu_id() * 2) as u16 // TODO: support S-mode contexts
}

/// IRQ# for preemption IPIs, delivered via the CLINT machine software interrupt.
pub const PREEMPT_IPI_IRQ: u16 = 0;

/// IRQ# for wakeup IPIs, delivered via the CLINT machine software interrupt.
///
/// PLIC sources are numbered 1..=1023, so this number never collides with a PLIC source.
pub const WAKEUP_IPI_IRQ: u16 = 1024;

/// IRQ# of the CLINT machine timer interrupt.
pub const TIMER_IRQ: u16 = 1025;

/// Maximum number of harts that can receive IPIs (QEMU `virt` supports up to 8).
const MAX_HARTS: usize = 8;

const PREEMPT_IPI_BIT: u8 = 1 << 0;
const WAKEUP_IPI_BIT: u8 = 1 << 1;

/// Software IPIs pending on each hart.
///
/// Each hart has a single machine software interrupt (MSIP), so the IPI kind is
/// recorded here before MSIP is raised, and read back by the receiving hart.
static PENDING_IPIS: [AtomicU8; MAX_HARTS] = [const { AtomicU8::new(0) }; MAX_HARTS];

#[inline]
const fn ipi_bit(irq: u16) -> Option<u8> {
    match irq {
        PREEMPT_IPI_IRQ => Some(PREEMPT_IPI_BIT),
        WAKEUP_IPI_IRQ => Some(WAKEUP_IPI_BIT),
        _ => None,
    }
}

/// Register the CLINT/PLIC interrupt controller.
///
/// # Safety
///
/// This function must be called only once by the primary CPU,
/// after the heap allocator has been initialized.
pub unsafe fn init_interrupt_controller() {
    interrupt::register_interrupt_controller(Box::new(InterruptController::qemu_virt()));
}

impl InterruptController {
    /// Record `bit` as pending on `hart_id` and raise its machine software interrupt.
    fn send_soft_ipi(&self, bit: u8, hart_id: usize) {
        let Some(pending) = PENDING_IPIS.get(hart_id) else {
            log::warn!("Failed to send IPI to CPU {hart_id}: unsupported hart ID");
            return;
        };

        pending.fetch_or(bit, Ordering::Release);
        if let Err(e) = self.clint.set_soft_interrupt(hart_id) {
            log::warn!("Failed to send IPI to CPU {hart_id}: {e:?}");
        }
    }
}

impl interrupt::InterruptController for InterruptController {
    #[inline]
    fn enable_irq(&mut self, irq: u16) {
        if ipi_bit(irq).is_some() {
            self.clint.enable_soft_interrupt();
        } else if irq == TIMER_IRQ {
            self.clint.enable_timer_interrupt();
        } else {
            let _ = self.plic.enable_interrupt(plic_context(), irq);
        }
    }

    #[inline]
    fn disable_irq(&mut self, irq: u16) {
        match irq {
            // The software interrupt is shared, so only the preemption IPI controls it.
            PREEMPT_IPI_IRQ => self.clint.disable_soft_interrupt(),
            WAKEUP_IPI_IRQ => (),
            TIMER_IRQ => self.clint.disable_timer_interrupt(),
            _ => {
                let _ = self.plic.disable_interrupt(plic_context(), irq);
            }
        }
    }

    #[inline]
    fn pending_irqs(&self) -> alloc::boxed::Box<dyn Iterator<Item = u16>> {
        let context = plic_context();
        let mut pending_irqs = alloc::vec::Vec::new();
        if self.clint.is_soft_interrupt_pending() {
            // Clear MSIP before taking the pending mask, so that an IPI sent
            // after the mask is taken raises MSIP again rather than being lost.
            self.clint.clear_soft_interrupt();
            let pending = PENDING_IPIS
                .get(cpu_id())
                .map_or(0, |p| p.swap(0, Ordering::Acquire));
            if pending & PREEMPT_IPI_BIT != 0 {
                pending_irqs.push(PREEMPT_IPI_IRQ);
            }
            if pending & WAKEUP_IPI_BIT != 0 {
                pending_irqs.push(WAKEUP_IPI_IRQ);
            }
        }
        if self.clint.is_timer_interrupt_pending() {
            // The machine timer interrupt is level-triggered; cancel it until
            // the timer is reset by its handler.
            self.clint.clear_timer();
            pending_irqs.push(TIMER_IRQ);
        }
        // Safety: context is in range
        while let Some(irq) = unsafe { self.plic.claim_interrupt_unchecked(context) } {
            pending_irqs.push(irq);
        }
        Box::new(pending_irqs.into_iter())
    }

    #[inline]
    fn send_ipi(&mut self, irq: u16, cpu_id: u32) {
        match ipi_bit(irq) {
            Some(bit) => self.send_soft_ipi(bit, cpu_id as usize),
            None => log::warn!("PLIC does not support sending IPIs, ignoring IRQ {irq}"),
        }
    }

    #[inline]
    fn send_ipi_broadcast(&mut self, irq: u16) {
        match ipi_bit(irq) {
            Some(bit) => (0..num_cpu()).for_each(|hart_id| self.send_soft_ipi(bit, hart_id)),
            None => log::warn!("PLIC does not support sending IPIs, ignoring IRQ {irq}"),
        }
    }

    #[inline]
    fn send_ipi_broadcast_without_self(&mut self, irq: u16) {
        match ipi_bit(irq) {
            Some(bit) => {
                let self_id = cpu_id();
                (0..num_cpu())
                    .filter(|&hart_id| hart_id != self_id)
                    .for_each(|hart_id| self.send_soft_ipi(bit, hart_id));
            }
            None => log::warn!("PLIC does not support sending IPIs, ignoring IRQ {irq}"),
        }
    }

    #[inline]
    fn irq_range(&self) -> (u16, u16) {
        // 0 and WAKEUP_IPI_IRQ are CLINT software IPIs, TIMER_IRQ is the CLINT timer,
        // and 1..=num_sources are PLIC
        (0, TIMER_IRQ + 1)
    }

    #[inline]
    fn irq_range_for_pnp(&self) -> (u16, u16) {
        // PLIC cannot be used for IPIs, so the range is 1..=num_sources
        (1, self.plic.num_sources + 1)
    }
}
