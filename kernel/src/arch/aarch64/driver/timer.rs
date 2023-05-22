// 
use awkernel_lib::interrupt;
use crate::arch::aarch64::types::KernelVirtualAddress;
use core::ptr;

use core::marker::PhantomData;

mod registers {
    pub const CONTROL: usize = 0x00;
    pub const COUNT_LOW: usize = 0x04;
    pub const COMPARE_1: usize = 0x10;
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


const SYS_TIMER: DeviceRegisters<u32> = DeviceRegisters::new(KernelVirtualAddress::new(0x3F00_0000));

pub struct SystemTimer;

impl SystemTimer {

    pub fn init(irq: usize) {
        log::info!("timer: initializing generic arm timer to trigger context switch");

        interrupt::register_irq(irq ,SystemTimer::handle_irq).unwrap();
        interrupt::enable_irq(irq);

        unsafe {
            let value = SYS_TIMER.get(registers::COUNT_LOW) + 20000;
            SYS_TIMER.set(registers::COMPARE_1, value);
        }
    }

    pub fn reset() {
        unsafe {
            SYS_TIMER.set(registers::CONTROL, 1 << 1);
            let value = SYS_TIMER.get(registers::COUNT_LOW) + 20000;
            SYS_TIMER.set(registers::COMPARE_1, value);
        }
        log::info!("20ms passed");

    }

    fn handle_irq() {
        SystemTimer::reset();

    }
}

