use alloc::boxed::Box;
use awkernel_lib::interrupt::InterruptController;
use core::ptr::{read_volatile, write_volatile};

/// RISC-V PLIC (Platform-Level Interrupt Controller) implementation
pub struct RiscvPlic {
    base_address: usize,
    max_priority: u32,
    num_sources: u16,
}

impl RiscvPlic {
    /// Create a new RISC-V PLIC controller
    pub const fn new(base_address: usize, num_sources: u16) -> Self {
        Self {
            base_address,
            max_priority: 7, // Typical PLIC priority levels: 0-7
            num_sources,
        }
    }

    /// Get the priority register address for a given interrupt source
    fn priority_reg(&self, source: u16) -> *mut u32 {
        (self.base_address + (source as usize * 4)) as *mut u32
    }

    /// Get the enable register address for a given context and interrupt source
    fn enable_reg(&self, context: usize, source: u16) -> *mut u32 {
        let reg_index = source as usize / 32;
        let base = self.base_address + 0x2000 + context * 0x80;
        (base + reg_index * 4) as *mut u32
    }

    /// Get the threshold register address for a given context
    fn threshold_reg(&self, context: usize) -> *mut u32 {
        (self.base_address + 0x200000 + context * 0x1000) as *mut u32
    }

    /// Get the claim register address for a given context
    fn claim_reg(&self, context: usize) -> *mut u32 {
        (self.base_address + 0x200004 + context * 0x1000) as *mut u32
    }

    /// Set priority for an interrupt source
    fn set_priority(&self, source: u16, priority: u32) {
        if source > 0 && source <= self.num_sources && priority <= self.max_priority {
            let reg = self.priority_reg(source);
            unsafe { write_volatile(reg, priority) };
        }
    }

    /// Enable interrupt for a specific context
    fn enable_interrupt(&self, context: usize, source: u16) {
        if source > 0 && source <= self.num_sources {
            let reg = self.enable_reg(context, source);
            let bit_pos = source as usize % 32;
            unsafe {
                let current = read_volatile(reg);
                write_volatile(reg, current | (1 << bit_pos));
            }
        }
    }

    /// Disable interrupt for a specific context
    fn disable_interrupt(&self, context: usize, source: u16) {
        if source > 0 && source <= self.num_sources {
            let reg = self.enable_reg(context, source);
            let bit_pos = source as usize % 32;
            unsafe {
                let current = read_volatile(reg);
                write_volatile(reg, current & !(1 << bit_pos));
            }
        }
    }

    /// Get the current hart ID (CPU ID)
    fn get_hart_id(&self) -> usize {
        // Use mhartid CSR to get hart ID
        let hart_id: usize;
        unsafe {
            core::arch::asm!("csrr {}, mhartid", out(reg) hart_id);
        }
        hart_id
    }

    /// Get supervisor mode context for current hart
    fn get_supervisor_context(&self) -> usize {
        // Typically supervisor mode context = hartid * 2 + 1
        self.get_hart_id() * 2 + 1
    }
}

impl InterruptController for RiscvPlic {
    fn enable_irq(&mut self, irq: u16) {
        // Set a reasonable priority for the interrupt
        self.set_priority(irq, 1);

        // Enable for supervisor mode (we're running in supervisor mode)
        let context = self.get_supervisor_context();
        self.enable_interrupt(context, irq);
    }

    fn disable_irq(&mut self, irq: u16) {
        let context = self.get_supervisor_context();
        self.disable_interrupt(context, irq);
    }

    fn pending_irqs(&self) -> Box<dyn Iterator<Item = u16>> {
        // Check pending interrupts by claiming them
        let context = self.get_supervisor_context();
        let claim_reg = self.claim_reg(context);

        let mut pending = alloc::vec::Vec::new();

        unsafe {
            let claimed = read_volatile(claim_reg);
            if claimed != 0 {
                pending.push(claimed as u16);
                // Complete the interrupt (write back the claim)
                write_volatile(claim_reg, claimed);
            }
        }

        Box::new(pending.into_iter())
    }

    fn send_ipi(&mut self, _irq: u16, _cpu_id: u32) {
        // RISC-V IPI is typically handled through software interrupts
        // This would require SBI (Supervisor Binary Interface) calls
        // For now, we'll leave this unimplemented as it depends on the SBI implementation
        log::warn!("RISC-V IPI not implemented yet");
    }

    fn send_ipi_broadcast(&mut self, _irq: u16) {
        log::warn!("RISC-V IPI broadcast not implemented yet");
    }

    fn send_ipi_broadcast_without_self(&mut self, _irq: u16) {
        log::warn!("RISC-V IPI broadcast without self not implemented yet");
    }

    fn init_non_primary(&mut self) {
        // Set threshold to 0 to accept all interrupts
        let context = self.get_supervisor_context();
        let threshold_reg = self.threshold_reg(context);
        unsafe { write_volatile(threshold_reg, 0) };
    }

    fn irq_range(&self) -> (u16, u16) {
        // PLIC interrupt sources typically range from 1 to num_sources
        (1, self.num_sources + 1)
    }

    fn irq_range_for_pnp(&self) -> (u16, u16) {
        // Reserve lower IRQs for system use, higher for PnP
        let start = self.num_sources / 2;
        (start, self.num_sources + 1)
    }
}
