use core::ptr::read_volatile;

use super::DeviceInfo;

mod registers {
    use awkernel_lib::{mmio_r, mmio_rw};

    mmio_rw!(offset 0x00 => pub MESSAGE_CONTROL_NEXT_PTR_CAP_ID<u32>);

    // MSI

    // Message Control Register
    pub const MSI_ENABLE: u32 = 1 << 16;
    pub const MSI_BIT64_ADDRESS_CAPABLE: u32 = 1 << (7 + 16);
    pub const MSI_PER_VECTOR_MASK_CAPABLE: u32 = 1 << (8 + 16);

    // MSI-X
    mmio_r!(offset 0x04 => pub MSIX_TABLE_OFFSET<u32>);
    mmio_r!(offset 0x04 => pub MSIX_PBA_OFFSET<u32>); // Pending Bit Array
}

#[derive(Debug)]
pub struct MSI {
    cap_ptr: usize,
    multiple_message_capable: MultipleMessage,
}

#[derive(Debug, Clone, Copy)]
pub enum MultipleMessage {
    One = 1,
    Two = 2,
    Four = 4,
    Eight = 8,
    Sixteen = 16,
    ThirtyTwo = 32,
}

/// # Message Signaled Interrupts (MSI)
///
/// ## Message Control Register
///
/// | Bits 15-9 | Bit 8              | Bit 7  | Bits 6-4                | Bits 3-1                 | Bit 0  |
/// |-----------|--------------------|--------|-------------------------|--------------------------|--------|
/// | Reserved  | Per-vector masking | 64-bit | Multiple Message Enable | Multiple Message Capable | Enable |
///
/// ## Multiple Message Enable (MME)
///
/// ### MME Register
///
/// | MME   | #Interrupts |
/// |-------|-------------|
/// | 0b000 | 1           |
/// | 0b001 | 2           |
/// | 0b010 | 4           |
/// | 0b011 | 8           |
/// | 0b100 | 16          |
/// | 0b101 | 32          |
///
/// ### Example of MME
///
/// 1. Allocation of Four Messages to the Device
///     - The device has been allocated four different messages for interrupt signaling.
///     - This means it can differentiate among four separate events or conditions for which it needs to notify the system.
/// 2 Message Data Register Value (49A0h)
///     - This value is assigned to the device's Message Data register.
///     - In MSI, the Message Data register typically contains the interrupt vector that the device should use when signaling an interrupt.
/// 3. Message Address Register Value (FEEF_F00Ch)
///     - This is the memory address into which the device writes its interrupt message.
///     - The address FEEF_F00Ch is typically associated with the local APIC (Advanced Programmable Interrupt Controller) in the system, which is responsible for handling interrupts.
/// 4. Event Signaling
///     - When an event occurs, the device signals this by writing a dword (double word, 32 bits) to the memory address specified in the Message Address register.
///     - The value written combines the base value from the Message Data register (49A0h) with an identifier for the specific event.
///     - The data value written will be one of 0000_49A0h, 0000_49A1h, 0000_49A2h, or 0000_49A3h.
///     - The modification of the lower two bits of the data value (49A0h, 49A1h, 49A2h, 49A3h) indicates which of the four events has occurred.
///     - The upper 16 bits of the message data (0000h) remain constant.
/// 5. Extended Capability for More Events
///     - If eight messages had been allocated, the lower three bits of the message data could be modified to represent one of the eight different events.
///     - This flexibility allows for more granular identification of different types of interrupts or conditions within the device.
impl MSI {
    pub fn new(cap_ptr: usize) -> Self {
        let multiple_message_capable = {
            let msg_cap = (registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.read(cap_ptr) >> 17) & 0b111;

            match msg_cap {
                0b000 => MultipleMessage::One,
                0b001 => MultipleMessage::Two,
                0b010 => MultipleMessage::Four,
                0b011 => MultipleMessage::Eight,
                0b100 => MultipleMessage::Sixteen,
                0b101 => MultipleMessage::ThirtyTwo,
                _ => unreachable!(),
            }
        };

        Self {
            cap_ptr,
            multiple_message_capable,
        }
    }

    pub fn enable(&mut self) {
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.setbits(registers::MSI_ENABLE, self.cap_ptr);
    }

    pub fn disable(&mut self) {
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.clrbits(registers::MSI_ENABLE, self.cap_ptr);
    }

    pub fn is_enabled(&self) -> bool {
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.read(self.cap_ptr) & registers::MSI_ENABLE != 0
    }

    pub fn get_multiple_message_capable(&self) -> MultipleMessage {
        self.multiple_message_capable
    }

    pub fn set_multipe_message_enable(&mut self, mme: MultipleMessage) -> Result<(), &'static str> {
        if mme as u32 > self.multiple_message_capable as u32 {
            return Err("The number of interrupts is too large.");
        }

        let reg = registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.read(self.cap_ptr);
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.write(
            (reg & !(0b111 << (16 + 4))) | ((mme as u32) << (16 + 4)),
            self.cap_ptr,
        );

        Ok(())
    }

    pub fn per_vector_mask_capable(&self) -> bool {
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.read(self.cap_ptr)
            & registers::MSI_PER_VECTOR_MASK_CAPABLE
            != 0
    }
}

/*
memo

https://qiita.com/v1471/items/47f275e530bec624795f

intc@8000000 {
    phandle = <0x8011>;
    reg = <0x0000000008000000 0x0000000000010000 0x00000000080a0000 0x0000000000f60000>;
    #redistributor-regions = <0x1>;
    compatible = "arm,gic-v3";
    ranges;
    #size-cells = <0x2>;
    #address-cells = <0x2>;
    interrupt-controller;
    #interrupt-cells = <0x3>;
    its@8080000 {
            phandle = <0x8012>;
            reg = <0x0000000008080000 0x0000000000020000>;
            msi-controller;
            compatible = "arm,gic-v3-its";
    };
};
*/
