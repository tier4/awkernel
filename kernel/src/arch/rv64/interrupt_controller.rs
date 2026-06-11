use alloc::boxed::Box;
use awkernel_lib::interrupt::InterruptController;
use core::ptr::{read_volatile, write_volatile};
use core::sync::atomic::{AtomicU64, Ordering};

/// RISC-V PLIC (Platform-Level Interrupt Controller) implementation
/// Combined with CLINT/ACLINT for IPI support
pub struct RiscvPlic {
    base_address: usize,
    max_priority: u32,
    num_sources: u16,
}

// CLINT/ACLINT base address for IPIs
const ACLINT_BASE: usize = 0x0200_0000;
const MSIP_OFFSET: usize = 0x0000; // Machine Software Interrupt Pending

/// Logical IRQ ID used for the local machine timer (MTIP).
///
/// The RISC-V timer is a local interrupt (mcause = 7), not a PLIC source, so this
/// ID is never claimed from the PLIC. It is delivered through `LOCAL_PENDING`
/// instead. It must lie within `irq_range()` so the timer handler can be
/// registered, be < 64 to fit the pending bitmask, and not collide with a PLIC
/// source actually wired on the platform (QEMU virt uses 1-8 for virtio, 10 for
/// UART, 32-35 for PCIe INTx).
pub const TIMER_IRQ: u16 = 63;

const MAX_HARTS: usize = awkernel_lib::cpu::NUM_MAX_CPU;

/// Per-hart pending bitmask for local (non-PLIC) interrupts: IPI reasons and the
/// local timer. MSIP is a single software-interrupt line per hart, so the sender
/// records the logical IRQ (e.g. PREEMPT_IRQ vs WAKEUP_IRQ) here before raising
/// MSIP, and `pending_irqs()` on the target hart drains it.
static LOCAL_PENDING: [AtomicU64; MAX_HARTS] = [const { AtomicU64::new(0) }; MAX_HARTS];

/// Record a pending local interrupt for `hart_id` so the next `pending_irqs()`
/// call on that hart reports `irq`.
pub(super) fn set_local_pending(hart_id: usize, irq: u16) {
    if hart_id < MAX_HARTS && irq < 64 {
        LOCAL_PENDING[hart_id].fetch_or(1 << irq, Ordering::Release);
    }
}

/// Local interrupts (IPIs, timer) are delivered via MSIP/MTIP and `LOCAL_PENDING`,
/// not the PLIC, so PLIC enable/disable must not touch their source numbers.
fn is_local_irq(irq: u16) -> bool {
    irq == crate::config::PREEMPT_IRQ || irq == crate::config::WAKEUP_IRQ || irq == TIMER_IRQ
}

// Import the detected CPU count from kernel_main
use super::kernel_main::NUM_CPUS;

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

    /// Get machine mode PLIC context for current hart (hartid * 2).
    /// S-mode context would be hartid * 2 + 1, but this kernel runs in M-mode.
    fn get_machine_context(&self) -> usize {
        self.get_hart_id() * 2
    }

    /// Send software interrupt (IPI) to a specific hart
    fn send_software_interrupt(&self, hart_id: u32) {
        // MSIP register for each hart is at ACLINT_BASE + MSIP_OFFSET + (hart_id * 4)
        let msip_addr = (ACLINT_BASE + MSIP_OFFSET + (hart_id as usize * 4)) as *mut u32;
        unsafe {
            write_volatile(msip_addr, 1);
        }
    }

    /// Enable machine software (MSIE, bit 3) and external (MEIE, bit 11) interrupts
    fn enable_machine_interrupts(&self) {
        unsafe {
            core::arch::asm!("csrrs {tmp}, mie, {val}", tmp = lateout(reg) _, val = in(reg) ((1usize << 3) | (1usize << 11)));
        }
    }

    /// Initialize the PLIC context for the primary hart.
    ///
    /// Sets the claim threshold to 0 (accept all priorities) and enables
    /// software/external interrupts in `mie`. Secondary harts get the same
    /// setup via `init_non_primary()`.
    pub fn init_primary(&self) {
        let context = self.get_machine_context();
        let threshold_reg = self.threshold_reg(context);
        unsafe { write_volatile(threshold_reg, 0) };

        self.enable_machine_interrupts();
    }
}

impl InterruptController for RiscvPlic {
    fn enable_irq(&mut self, irq: u16) {
        // Local interrupts (IPIs, timer) are not routed through the PLIC.
        if is_local_irq(irq) {
            return;
        }

        // Set a reasonable priority for the interrupt
        self.set_priority(irq, 1);

        let context = self.get_machine_context();
        self.enable_interrupt(context, irq);
    }

    fn disable_irq(&mut self, irq: u16) {
        if is_local_irq(irq) {
            return;
        }

        let context = self.get_machine_context();
        self.disable_interrupt(context, irq);
    }

    fn pending_irqs(&self) -> Box<dyn Iterator<Item = u16>> {
        let mut pending = alloc::vec::Vec::new();

        // Local interrupts first: IPI reasons recorded by send_ipi() and the
        // local timer (recorded by the M-mode trap handler).
        let hart_id = self.get_hart_id();
        if hart_id < MAX_HARTS {
            let mut local = LOCAL_PENDING[hart_id].swap(0, Ordering::Acquire);
            while local != 0 {
                let irq = local.trailing_zeros() as u16;
                pending.push(irq);
                local &= local - 1;
            }
        }

        // Then drain all pending PLIC external interrupts by claiming until the
        // claim register reads 0, so multiple pending sources are not starved.
        let context = self.get_machine_context();
        let claim_reg = self.claim_reg(context);

        loop {
            let claimed = unsafe { read_volatile(claim_reg) };
            if claimed == 0 {
                break;
            }
            pending.push(claimed as u16);
            // Complete the interrupt (write back the claim)
            unsafe { write_volatile(claim_reg, claimed) };
        }

        Box::new(pending.into_iter())
    }

    fn send_ipi(&mut self, irq: u16, cpu_id: u32) {
        // Record the logical IRQ for the target hart, then raise its MSIP.
        set_local_pending(cpu_id as usize, irq);
        self.send_software_interrupt(cpu_id);
    }

    fn send_ipi_broadcast(&mut self, irq: u16) {
        // Send IPI to all CPUs
        let num_cpus = NUM_CPUS.load(Ordering::Acquire) as u32;
        for cpu_id in 0..num_cpus {
            set_local_pending(cpu_id as usize, irq);
            self.send_software_interrupt(cpu_id);
        }
    }

    fn send_ipi_broadcast_without_self(&mut self, irq: u16) {
        // Send IPI to all CPUs except current
        let current_hart = self.get_hart_id() as u32;
        let num_cpus = NUM_CPUS.load(Ordering::Acquire) as u32;
        for cpu_id in 0..num_cpus {
            if cpu_id != current_hart {
                set_local_pending(cpu_id as usize, irq);
                self.send_software_interrupt(cpu_id);
            }
        }
    }

    fn init_non_primary(&mut self) {
        // Set threshold to 0 to accept all interrupts
        let context = self.get_machine_context();
        let threshold_reg = self.threshold_reg(context);
        unsafe { write_volatile(threshold_reg, 0) };

        // Enable software interrupts (IPIs) and external interrupts (PLIC)
        self.enable_machine_interrupts();
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
