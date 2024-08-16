# Console

`Console` is a trait for the console and defined in [awkernel_lib/src/console.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/console.rs) as follows.

```rust
pub trait Console: Write + Send {
    /// Enable the serial port.
    fn enable(&mut self);

    /// Disable the serial port.
    fn disable(&mut self);

    /// Enable the reception interrupt.
    fn enable_recv_interrupt(&mut self);

    /// Disable the reception interrupt.
    fn disable_recv_interrupt(&mut self);

    /// Acknowledge to the reception interrupt.
    fn acknowledge_recv_interrupt(&mut self);

    /// Get IRQ#.
    fn irq_id(&self) -> u16;

    /// Read a byte.
    fn get(&mut self) -> Option<u8>;

    /// Write a byte.
    fn put(&mut self, data: u8);
}
```

There are several functions regarding the `Console` trait in [awkernel_lib/src/console.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/console.rs).


|  function             | description |
|-----------------------|-------------|
| `fn register_unsafe_puts(console: unsafe fn(&str))` | Register the unsafe `puts` function. |
| `unsafe fn unsafe_puts(data: &str)` | Write a string. |
| `unsafe fn unsafe_print_hex_u32(num: u32)` | Write a hexadecimal number. |
| `unsafe fn unsafe_print_hex_u64(num: u64)` | Write a hexadecimal number. |
| `unsafe fn unsafe_print_hex_u96(num: u128)` | Write a hexadecimal number. |
| `unsafe fn unsafe_print_hex_u128(num: u128)` | Write a hexadecimal number. |
| `fn register_console(console: Box<dyn Console>)` | Register the console. |
| `fn enable()` | Enable the console. |
| `fn disable()` | Disable the console. |
| `fn enable_recv_interrupt()` | Enable the reception interrupt. |
| `fn disable_recv_interrupt()` | Disable the reception interrupt. |
| `fn acknowledge_recv_interrupt()` | Acknowledge to the reception interrupt. |
| `fn irq_id()` | Get IRQ#. |
| `fn get()` | Read a byte. |
| `fn put(data: u8)` | Write a byte. |
| `fn print(data: &str)` | Write a string. |

When booting, an unsafe console should be registered by calling the `register_unsafe_puts` function.
After that, the `unsafe_puts` and `unsafe_print_hex` functions can be used to print messages.
Note that these functions are unsafe because they may cause data races.

After enabling mutual exclusion, a safe console should be registered by calling the `register_console` function.
Then, the `print`, `get`, and `put` functions can be used to print messages.

# Implementation

## x86_64

x86_64 should equip UART 16550 serial ports, and Awkerenel uses the serial port to output messages as a console.
UART 16550's device driver is implemented in [awkernel_drivers/src/uart/uart_16550](https://github.com/tier4/awkernel/tree/main/awkernel_drivers/src/uart/uart_16550)
whose original source code is from [uart_16550](https://github.com/rust-osdev/uart_16550).
The `Uart` structure defined in
[kernel/src/arch/x86_64/console.rs](https://github.com/tier4/awkernel/blob/main/kernel/src/arch/x86_64/console.rs)
implements the `Console` trait as follows.

```rust
pub struct Uart {
    port: uart_16550::SerialPort,
    enabled: bool,
}

impl Console for Uart {
    fn enable(&mut self) {
        self.enabled = true;
    }

    fn disable(&mut self) {
        self.enabled = false;
    }

    fn enable_recv_interrupt(&mut self) {
        self.port.enable_interrupt();
    }

    fn disable_recv_interrupt(&mut self) {
        self.port.disable_interrupt();
    }

    fn acknowledge_recv_interrupt(&mut self) {
        // nothing to do
    }

    fn irq_id(&self) -> u16 {
        36 // COM1
    }

    fn get(&mut self) -> Option<u8> {
        if self.enabled {
            self.port.try_receive()
        } else {
            None
        }
    }

    fn put(&mut self, data: u8) {
        if self.enabled {
            self.port.send(data);
        }
    }
}
```

## AArch64

AArch64 should equip PL011 UART serial ports, and Awkerenel uses the serial port to output messages as a console.
PL011 UART's device driver is implemented in [awkernel_drivers/src/uart/pl011.rs](https://github.com/tier4/awkernel/blob/main/awkernel_drivers/src/uart/pl011.rs),
and it implements the `Console` trait as follows.

```rust
impl Console for PL011 {
    fn enable(&mut self) {
        use registers::CR;
        registers::UART0_CR.write(CR::EN | CR::RXE | CR::TXE, self.base_addr); // enable, Rx, Tx
    }

    fn disable(&mut self) {
        registers::UART0_CR.write(registers::CR::empty(), self.base_addr);
    }

    fn enable_recv_interrupt(&mut self) {
        registers::UART0_IMSC.setbits(IMSC_RXIM, self.base_addr);
    }

    fn disable_recv_interrupt(&mut self) {
        registers::UART0_IMSC.clrbits(IMSC_RXIM, self.base_addr);
    }

    fn acknowledge_recv_interrupt(&mut self) {
        registers::UART0_ICR.write(registers::ICR::RXIC, self.base_addr);
    }

    fn irq_id(&self) -> u16 {
        self.irq
    }

    fn get(&mut self) -> Option<u8> {
        if registers::UART0_FR.read(self.base_addr) & 0x10 != 0 {
            None
        } else {
            Some(registers::UART0_DR.read(self.base_addr) as u8)
        }
    }

    fn put(&mut self, data: u8) {
        // wait until we can send
        unsafe { asm!("nop;") };
        while registers::UART0_FR.read(self.base_addr) & 0x20 != 0 {
            core::hint::spin_loop();
        }

        // write the character to the buffer
        registers::UART0_DR.write(data as u32, self.base_addr);
    }
}
```
