# Interrupt Controller

`InterruptController` is a trait for interrupt controllers.
It is defined in [awkernel_lib/src/interrupt.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/interrupt.rs) as follows.

```rust
pub trait InterruptController: Sync + Send {
    fn enable_irq(&mut self, irq: u16);
    fn disable_irq(&mut self, irq: u16);
    fn pending_irqs(&self) -> Box<dyn Iterator<Item = u16>>;

    /// Send an inter-process interrupt to `target` CPU.
    fn send_ipi(&mut self, irq: u16, cpu_id: u32);

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
| `fn send_ipi(irq: u16, cpu_id: u32)` | Send an inter-process interrupt to `cpu_id` CPU. |
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

`handle_irq` is called in interrupt handlers defined in.
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

## RISC-V 64-bit (RV64)

For RV64, traps are taken in machine mode by a low-level handler installed into `mtvec`
during boot in [kernel/src/arch/rv64/boot.S](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/rv64/boot.S).
The handler reads `mcause` to distinguish exceptions from interrupts and dispatches on the
interrupt code: a machine timer interrupt (code 7) and a machine software interrupt / IPI
(code 3) are handled, while other causes return without action.

```asm
early_trap_handler:
  csrr t0, mcause
  blt t0, zero, handle_interrupt   # MSB set => interrupt
  j unhandled_trap

handle_interrupt:
  # ... mask off the interrupt code ...
  li t1, 7                         # M-mode timer interrupt
  beq t0, t1, handle_timer_interrupt
  li t1, 3                         # M-mode software interrupt (IPI)
  beq t0, t1, handle_software_interrupt
```

After saving the clobbered registers, the timer path calls `riscv_handle_timer` and the
IPI path calls `riscv_handle_ipi`. Both are defined in
[kernel/src/arch/rv64/kernel_main.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/rv64/kernel_main.rs)
and forward to the architecture-independent `handle_irqs`:

```rust
/// M-mode software interrupt (IPI) handler called from assembly.
pub extern "C" fn riscv_handle_ipi() {
    awkernel_lib::interrupt::handle_irqs(true);
}

/// M-mode timer interrupt handler called from assembly.
pub extern "C" fn riscv_handle_timer() {
    awkernel_lib::interrupt::handle_irqs(true);
}
```

The software-interrupt (`MSIP`) bit is cleared in assembly before returning, and the timer
is re-armed by the registered timer handler.

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

## RISC-V 64-bit (RV64)

For RV64, external interrupts are managed by the **PLIC** (Platform-Level Interrupt
Controller), and inter-processor interrupts (IPIs) are delivered through the
**CLINT/ACLINT** software-interrupt (`MSIP`) registers. Both are implemented by the
`RiscvPlic` structure in
[kernel/src/arch/rv64/interrupt_controller.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/rv64/interrupt_controller.rs).

```rust
/// RISC-V PLIC (Platform-Level Interrupt Controller) implementation.
/// Combined with CLINT/ACLINT for IPI support.
pub struct RiscvPlic {
    base_address: usize,
    max_priority: u32,
    num_sources: u16,
}

// CLINT/ACLINT base address for IPIs.
const ACLINT_BASE: usize = 0x0200_0000;
const MSIP_OFFSET: usize = 0x0000; // Machine Software Interrupt Pending
```

The PLIC register layout is computed relative to `base_address`:

| register | address | purpose |
|----------|---------|---------|
| priority | `base + source * 4` | per-source interrupt priority (0-7) |
| enable | `base + 0x2000 + context * 0x80` | per-context enable bitmap |
| threshold | `base + 0x200000 + context * 0x1000` | per-context priority threshold |
| claim/complete | `base + 0x200004 + context * 0x1000` | claim a pending IRQ / signal completion |

The PLIC *context* for the running hart is computed as `hartid * 2 + 1` (the
supervisor-mode context), where the hart ID is read from the `mhartid` CSR.

`RiscvPlic` implements the [`InterruptController`](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/interrupt.rs) trait:

- `enable_irq` sets the source priority to `1` and sets its bit in the enable register.
- `disable_irq` clears the source's bit in the enable register.
- `pending_irqs` reads the claim register; a non-zero value is the claimed IRQ, which is
  immediately written back to the claim register to signal completion.
- `send_ipi` writes `1` to the target hart's `MSIP` register; the broadcast variants do so
  for every hart (skipping the sender for `send_ipi_broadcast_without_self`).
- `init_non_primary` sets the context threshold to `0` (accept all priorities) and enables
  machine software interrupts (`mie.MSIE`) so the core can receive IPIs.

```rust
impl InterruptController for RiscvPlic {
    fn enable_irq(&mut self, irq: u16) {
        self.set_priority(irq, 1);
        let context = self.get_supervisor_context();
        self.enable_interrupt(context, irq);
    }

    fn pending_irqs(&self) -> Box<dyn Iterator<Item = u16>> {
        let context = self.get_supervisor_context();
        let claim_reg = self.claim_reg(context);
        let mut pending = alloc::vec::Vec::new();
        unsafe {
            let claimed = read_volatile(claim_reg);
            if claimed != 0 {
                pending.push(claimed as u16);
                write_volatile(claim_reg, claimed); // Complete the interrupt.
            }
        }
        Box::new(pending.into_iter())
    }

    // ... send_ipi / init_non_primary / irq_range omitted ...
}
```

The controller is instantiated and registered during boot in
[kernel/src/arch/rv64/kernel_main.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/rv64/kernel_main.rs),
with the PLIC mapped at `0x0c00_0000` and 128 interrupt sources:

```rust
const PLIC_BASE: usize = 0x0c000000;
const NUM_SOURCES: u16 = 128;

let plic = Box::new(RiscvPlic::new(PLIC_BASE, NUM_SOURCES));
awkernel_lib::interrupt::register_interrupt_controller(plic);
```

## RISC-V 32-bit (RV32)

For RV32, a PLIC-based `InterruptController` is not yet implemented;
[awkernel_lib/src/arch/rv32/interrupt.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/rv32/interrupt.rs)
currently provides only the low-level enable/disable of interrupts via the `sstatus` CSR.
