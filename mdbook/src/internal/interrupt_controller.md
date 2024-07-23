# Interrupt Controller

The `InterruptController` is a trait for interrupt controllers.
It is defined in [awkernel_lib/src/interrupt.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/interrupt.rs) as follows.

```rust
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
```

Some related functions are defined in [awkernel_lib/src/interrupt.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/interrupt.rs) as follows.

|  function             | description |
|-----------------------|-------------|
| `fn register_handler<F>(...) -> Result<(), &'static str>` | Register a handler for the interrupt. |
| `fn get_handlers() -> BTreeMap<u16, Cow<'static, str>>` | Return the list of IRQs and their handlers. |
| `fn enable_irq(irq: u16)` | Enable the interrupt. |
| `fn disable_irq(irq: u16)` | Disable the interrupt. |
| `fn send_ipi(irq: u16, target: u32)` | Send an inter-process interrupt to `target` CPU. |
| `fn send_ipi_broadcast(irq: u16)` | Send an inter-process interrupt to all CPUs. |
| `fn send_ipi_broadcast_without_self(irq: u16)` | Send an inter-process interrupt to all CPUs except the sender CPU. |
| `fn register_handler_pcie_msi<F>(...) -> Result<IRQ, &'static str>` | Register a handler for PCIe MSI or MSI-X interrupt. |
| `fn handle_irq(irq: u16)` | Handle the interrupt. |
| `fn handle_irqs()` | Handle all pending interrupts. |
| `fn enable()` | Enable interrupts. |
| `fn disable()` | Disable interrupts. |
| `fn eoi()` | End of interrupt. |
| `fn handle_preemption()` | Handle preemption. |
| `fn set_preempt_irq(irq: u16, preemption: unsafe fn())` | Set the preemption handler. |
| `fn get_preempt_irq() -> u16`| Return the IRQ number for preemption. |

# Handling Interrupts

## x86_64

`handle_irq()` is called in interrupt handlers defined in.
[kernel/src/arch/x86_64/interrupt_handler.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/x86_64/interrupt_handler.rs) for x86_64 as follows.

```rust
macro_rules! irq_handler {
    ($name:ident, $id:expr) => {
        extern "x86-interrupt" fn $name(_stack_frame: InterruptStackFrame) {
            awkernel_lib::interrupt::eoi(); // End of interrupt.
            awkernel_lib::interrupt::handle_irq($id);
        }
    };
}
```

`irq_handler` macro is called in each interrupt handler.

## AArch64

The `handle_irqs` function is called in interrupt handlers defined in.
[kernel/src/arch/aarch64/exception.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/aarch64/exception.rs) for aarch64 as follows.

```rust
#[no_mangle]
pub extern "C" fn curr_el_spx_irq_el1(_ctx: *mut Context, _sp: usize, _esr: usize) {
    interrupt::handle_irqs();
}
```

# Handling Preemption

A preemption request can be sent by an inter process interrupt (IPI) to the target CPU.
This means that the target CPU should handle the preemption request if it receives the IPI.

## x86_64

For x86_64, the `handle_preempt` function is called in a interrupt handler defined in
[kernel/src/arch/x86_64/interrupt_handler.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/x86_64/interrupt_handler.rs) as follows.

```rust
extern "x86-interrupt" fn preemption(_stack_frame: InterruptStackFrame) {
    awkernel_lib::interrupt::eoi(); // End of interrupt.
    awkernel_lib::interrupt::handle_preemption();
}
```

## AArch64

For AArch64, handling preemption is performed in the `handle_irqs` function defined in
[awkernel_lib/src/interrupt.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/interrupt.rs).

```rust
/// Handle all pending interrupt requests.
/// This function will be used by only aarch64 and called from CPU's interrupt handlers.
#[cfg(feature = "aarch64")]
pub fn handle_irqs() {
    use crate::{heap, unwind::catch_unwind};
    use core::mem::transmute;

    let handlers = IRQ_HANDLERS.read();
    let mut need_preemption = false;

    // omitted

    if need_preemption {
        let ptr = PREEMPT_FN.load(Ordering::Relaxed);
        let preemption = unsafe { transmute::<*mut (), fn()>(ptr) };
        preemption();
    }
}
```


# Implementation

There are some device drivers for interrupt controllers in [awkernel_drivers/src/interrupt_controller](https://github.com/tier4/awkernel/tree/main/awkernel_drivers/src/interrupt_controller).

## x86_64

xAPIC and x2APIC are supported for x86_64.

- [xAPIC and x2APIC](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/interrupt_controller/apic.rs)


## AArch64

BCM2835's (Raspberry Pi 3) interrupt controller, GICv2 and GICv3 are supported for AAarch64.

- [BCM2835's interrupt controller](https://github.com/tier4/awkernel/tree/main/awkernel_drivers/src/interrupt_controller/bcm2835.rs)
- [GICv2](https://github.com/tier4/awkernel/tree/main/awkernel_drivers/src/interrupt_controller/gicv2.rs)
- [GICv3](https://github.com/tier4/awkernel/tree/main/awkernel_drivers/src/interrupt_controller/gicv3.rs)
