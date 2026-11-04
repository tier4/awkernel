use super::{clint::Clint, plic::Plic};
use crate::{cpu::cpu_id, interrupt};
use alloc::boxed::Box;

// TODO: get info from device tree
static INTERRUPT_CONTROLLER: InterruptController = InterruptController {
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
};

pub struct InterruptController {
    clint: Clint,
    plic: Plic,
}

#[inline]
pub(super) const fn clint() -> &'static Clint {
    &INTERRUPT_CONTROLLER.clint
}

impl interrupt::InterruptController for InterruptController {
    #[inline]
    fn enable_irq(&mut self, irq: u16) {
        match irq {
            0 => self.clint.enable_soft_interrupt(),
            _ => {
                let context = cpu_id() as u16; // TODO: support S-mode contexts
                let _ = self.plic.enable_interrupt(context, irq);
            }
        }
    }

    #[inline]
    fn disable_irq(&mut self, irq: u16) {
        match irq {
            0 => self.clint.disable_soft_interrupt(),
            _ => {
                let context = cpu_id() as u16; // TODO: support S-mode contexts
                let _ = self.plic.disable_interrupt(context, irq);
            }
        }
    }

    #[inline]
    fn pending_irqs(&self) -> alloc::boxed::Box<dyn Iterator<Item = u16>> {
        let context = cpu_id() as u16; // TODO: support S-mode contexts
        let mut pending_irqs = alloc::vec::Vec::new();
        if self.clint.is_soft_interrupt_pending() {
            self.clint.clear_soft_interrupt();
            pending_irqs.push(0);
        }
        // Safety: context is in range
        while let Some(irq) = unsafe { self.plic.claim_interrupt_unchecked(context) } {
            pending_irqs.push(irq);
        }
        Box::new(pending_irqs.into_iter())
    }

    #[inline]
    fn send_ipi(&mut self, irq: u16, cpu_id: u32) {
        if irq == 0 {
            if let Err(e) = self.clint.set_soft_interrupt(cpu_id as _) {
                log::warn!("Failed to send IPI to CPU {}: {:?}", cpu_id, e);
            }
        } else {
            log::warn!("PLIC does not support sending IPIs, ignoring IRQ {}", irq);
        }
    }

    #[inline]
    fn send_ipi_broadcast(&mut self, irq: u16) {
        if irq == 0 {
            self.clint.set_soft_interrupt_broadcast();
        } else {
            log::warn!("PLIC does not support sending IPIs, ignoring IRQ {}", irq);
        }
    }

    #[inline]
    fn send_ipi_broadcast_without_self(&mut self, irq: u16) {
        if irq == 0 {
            self.clint.set_soft_interrupt_broadcast_without_self();
        } else {
            log::warn!("PLIC does not support sending IPIs, ignoring IRQ {}", irq);
        }
    }

    #[inline]
    fn irq_range(&self) -> (u16, u16) {
        // 0 is CLINT, 1..=num_sources are PLIC
        (0, self.plic.num_sources + 1)
    }

    #[inline]
    fn irq_range_for_pnp(&self) -> (u16, u16) {
        // PLIC cannot be used for IPIs, so the range is 1..=num_sources
        (1, self.plic.num_sources + 1)
    }
}
