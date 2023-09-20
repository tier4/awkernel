//! | IRQ#     |             |
//! |----------|-------------|
//! |  0 -  31 | Mailbox0    |
//! | 32 -  64 | IRQ Basic   |
//! | 64 - 127 | IRQ1 / IRQ1 |

use alloc::boxed::Box;
use awkernel_lib::interrupt::InterruptController;

mod registers {
    use awkernel_lib::{mmio_r, mmio_rw, mmio_w};
    use bitflags::bitflags;

    mmio_r!(offset 0x00 => pub IRQ_BASIC_PENDING<u32>);
    mmio_r!(offset 0x04 => pub IRQ_PENDING1<u32>);
    mmio_r!(offset 0x08 => pub IRQ_PENDING2<u32>);
    mmio_r!(offset 0x0C => pub FIQ_CONTROL<u32>);
    mmio_w!(offset 0x10 => pub IRQ_ENABLE1<u32>);
    mmio_w!(offset 0x14 => pub IRQ_ENABLE2<u32>);
    mmio_w!(offset 0x18 => pub IRQ_ENABLE_BASIC<u32>);
    mmio_w!(offset 0x1C => pub IRQ_DISABLE1<u32>);
    mmio_w!(offset 0x20 => pub IRQ_DISABLE2<u32>);
    mmio_w!(offset 0x24 => pub IRQ_DISABLE_BASIC<u32>);

    mmio_w!(offset 0x50 => pub MAILBOX0_CONTROL<MailboxControl>);
    mmio_w!(offset 0x80 => pub MAILBOX0_WRITE_SET<u32>);
    mmio_rw!(offset 0xC0 => pub MAILBOX0_READ_AND_CLEAR<u32>);

    bitflags! {
        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        pub struct MailboxControl: u32 {
            const Mailbox3FIQ = 1 << 7;
            const Mailbox2FIQ = 1 << 6;
            const Mailbox1FIQ = 1 << 5;
            const Mailbox0FIQ = 1 << 4;
            const Mailbox3IRQ = 1 << 3;
            const Mailbox2IRQ = 1 << 2;
            const Mailbox1IRQ = 1 << 1;
            const Mailbox0IRQ = 1 << 0;
        }
    }
}

pub struct BCM2835IntCtrl {
    base: usize,
    local_base: usize,
}

impl BCM2835IntCtrl {
    pub fn new(base: usize, local_base: usize) -> Self {
        log::info!("BCM2835 IRQ: Initializing the interrupt controller.");

        let gic = Self { base, local_base };

        registers::IRQ_DISABLE1.write(!0, base);
        registers::IRQ_DISABLE2.write(!0, base);
        registers::IRQ_DISABLE_BASIC.write(!0, base);
        registers::IRQ_PENDING1.read(base);
        registers::IRQ_PENDING2.read(base);
        registers::IRQ_BASIC_PENDING.read(base);

        gic
    }

    pub fn iter(&self) -> PendingInterruptIterator {
        let pending = [
            {
                let cpu_id = awkernel_lib::cpu::cpu_id();
                let local_base = self.local_base + 16 * cpu_id;
                let bits = registers::MAILBOX0_READ_AND_CLEAR.read(local_base);
                registers::MAILBOX0_READ_AND_CLEAR.write(bits, local_base);
                bits
            },
            registers::IRQ_BASIC_PENDING.read(self.base),
            registers::IRQ_PENDING1.read(self.base),
            registers::IRQ_PENDING2.read(self.base),
        ];

        PendingInterruptIterator { next: 0, pending }
    }
}

impl InterruptController for BCM2835IntCtrl {
    fn enable_irq(&mut self, irq: u16) {
        let bit = (irq & (32 - 1)) as u32;
        let cpu_id = awkernel_lib::cpu::cpu_id();

        match irq {
            irq if irq < 32 => registers::MAILBOX0_CONTROL.write(
                registers::MailboxControl::Mailbox0IRQ,
                self.local_base + cpu_id * 4,
            ),
            irq if irq < 64 => registers::IRQ_ENABLE_BASIC.write(1 << bit, self.base),
            irq if irq < 96 => registers::IRQ_ENABLE1.write(1 << bit, self.base),
            irq if irq < 128 => registers::IRQ_ENABLE2.write(1 << bit, self.base),
            _ => log::warn!(
                "BCM2835 IRQ: Failed to enable IRQ #{irq} because it is greater than 127."
            ),
        }

        log::info!("BCM2835 IRQ: IRQ #{irq} has been enabled.");
    }

    fn disable_irq(&mut self, irq: u16) {
        let bit = (irq & (32 - 1)) as u32;
        let cpu_id = awkernel_lib::cpu::cpu_id();

        match irq {
            irq if irq < 32 => registers::MAILBOX0_CONTROL.write(
                registers::MailboxControl::empty(),
                self.local_base + cpu_id * 4,
            ),
            irq if irq < 64 => registers::IRQ_DISABLE_BASIC.write(1 << bit, self.base),
            irq if irq < 96 => registers::IRQ_DISABLE1.write(1 << bit, self.base),
            irq if irq < 128 => registers::IRQ_DISABLE2.write(1 << bit, self.base),
            _ => log::warn!(
                "BCM2835 IRQ: Failed to disable IRQ #{irq} because it is greater than 127."
            ),
        }

        log::info!("BCM2835 IRQ: IRQ #{irq} has been disabled.");
    }

    fn pending_irqs(&self) -> Box<dyn Iterator<Item = u16>> {
        Box::new(self.iter())
    }

    fn send_ipi(&mut self, irq: u16, target: u16) {
        assert!(irq < 32);

        registers::MAILBOX0_WRITE_SET
            .write(1 << irq as u32, self.local_base + 16 * (target as usize));
    }

    fn send_ipi_broadcast(&mut self, irq: u16) {
        for i in 0..awkernel_lib::cpu::num_cpu() {
            self.send_ipi(irq, i as u16);
        }
    }

    fn send_ipi_broadcast_without_self(&mut self, irq: u16) {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        for i in 0..awkernel_lib::cpu::num_cpu() {
            if i != cpu_id {
                self.send_ipi(irq, i as u16);
            }
        }
    }

    fn init_non_primary(&mut self) {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        registers::MAILBOX0_READ_AND_CLEAR.write(!0, self.local_base + cpu_id * 16);

        registers::MAILBOX0_CONTROL.write(
            registers::MailboxControl::Mailbox0IRQ,
            self.local_base + cpu_id * 4,
        );
    }
}

pub struct PendingInterruptIterator {
    next: usize,
    pending: [u32; 4],
}

impl Iterator for PendingInterruptIterator {
    type Item = u16;

    fn next(&mut self) -> Option<Self::Item> {
        let mut index = match self.next {
            x if x < 32 => 0,
            x if x < 64 => 1,
            x if x < 96 => 2,
            x if x < 128 => 3,
            _ => return None,
        };

        let mut bit = self.next & (32 - 1); // == next % 32

        while self.pending[index] & (1 << bit) == 0 {
            bit += 1;
            if bit >= 32 {
                bit = 0;
                index += 1;
                if index > 3 {
                    return None;
                }
            }
        }

        self.next = index * 32 + bit + 1;
        Some((index * 32 + bit) as u16)
    }
}
