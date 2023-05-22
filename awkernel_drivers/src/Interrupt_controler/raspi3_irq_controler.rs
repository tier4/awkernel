

use core::ptr;
use awkernel_lib::types::KernelVirtualAddress;
use core::marker::PhantomData;
use awkernel_lib::interrupt::InterruptController;

mod registers {
    pub const IRQ_PENDING1: usize = 0x04;
    pub const IRQ_PENDING2: usize = 0x08;
    pub const IRQ_ENABLE1: usize = 0x10;
    pub const IRQ_ENABLE2: usize = 0x14;
    pub const IRQ_DISABLE1: usize = 0x1C;
    pub const IRQ_DISABLE2: usize = 0x20;
}


pub struct DeviceRegisters<T> {
    base: KernelVirtualAddress,
    data: PhantomData<T>,
}

impl<T> DeviceRegisters<T> {
    pub const fn new(base: KernelVirtualAddress) -> Self {
        Self {
            base,
            data: PhantomData,
        }
    }

    pub unsafe fn get(&self, reg: impl Into<usize>) -> T {
        ptr::read_volatile(self.base.add(reg.into()).as_ptr::<T>())
    }

    pub unsafe fn set(&self, reg: impl Into<usize>, data: T) {
        ptr::write_volatile(self.base.add(reg.into()).as_mut::<T>(), data);
    }
}

pub struct GenericInterruptController {
    registers: DeviceRegisters<u32>,
    iter: Option<PendingInterruptIterator>,
}

impl GenericInterruptController {
    pub fn new() -> Self {
        // log::info!("interrupts: initializing generic arm interrupt controller");

        let gic = Self {
            registers: DeviceRegisters::new(KernelVirtualAddress::new(0x3F00_B200)),
            iter: None,
        };

        unsafe {
            gic.registers.set(registers::IRQ_DISABLE1, !0);
            gic.registers.set(registers::IRQ_DISABLE2, !0);
        }

        gic
    }

    pub fn iter(&mut self) -> PendingInterruptIterator {
        let pending = unsafe {
            [self.registers.get(registers::IRQ_PENDING1), self.registers.get(registers::IRQ_PENDING2)]
        };

        PendingInterruptIterator {
            next: 0,
            pending: pending,
        }
    }
}

impl InterruptController for GenericInterruptController {
    fn enable_irq(&mut self, irq: usize) {
        unsafe {
            if irq < 32 {
                self.registers.set(registers::IRQ_ENABLE1, 1 << irq);
            } else {
                self.registers.set(registers::IRQ_ENABLE2, 1 << (irq - 32));
            }
        }
    }

    fn disable_irq(&mut self, irq: usize) {
        unsafe {
            if irq < 32 {
                self.registers.set(registers::IRQ_DISABLE1, 1 << irq);
            } else {
                self.registers.set(registers::IRQ_DISABLE2, 1 << (irq - 32));
            }
        }
    }

    fn pending_irqs(&mut self) -> &mut dyn Iterator<Item=usize> {
        self.iter = Some(self.iter());
        self.iter.as_mut().unwrap()
    }
}


pub struct PendingInterruptIterator {
    next: usize,
    pending: [u32; 2],
}

impl Iterator for PendingInterruptIterator {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        let (mut index, mut bit) = if self.next < 32 {
            (0, self.next)
        } else {
            (1, self.next - 32)
        };

        while self.pending[index] & (1 << bit) == 0 {
            bit += 1;
            if bit >= 32 {
                bit = 0;
                index += 1;
                if index >= 2 {
                    return None;
                }
            }
        }

        self.next = index * 32 + bit + 1;
        Some(index * 32 + bit)
    }
}

