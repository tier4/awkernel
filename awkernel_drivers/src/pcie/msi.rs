mod registers {
    use awkernel_lib::{mmio_r, mmio_rw};

    mmio_rw!(offset 0x00 => pub MESSAGE_CONTROL_NEXT_PTR_CAP_ID<u32>);

    // Message Control Register
    pub const CTRL_ENABLE: u32 = 1 << 16;
    pub const CTRL_BIT64_ADDRESS_CAPABLE: u32 = 1 << (7 + 16);
    pub const CTRL_PER_VECTOR_MASK_CAPABLE: u32 = 1 << (8 + 16);

    mmio_rw!(offset 0x04 => pub MESSAGE_ADDRESS_32<u32>);
    mmio_rw!(offset 0x08 => pub MESSAGE_DATA_32<u32>);
    mmio_rw!(offset 0x0c => pub MASK_BITS_32<u32>);
    mmio_r!(offset 0x10 => pub PENDING_BITS_32<u32>);

    mmio_rw!(offset 0x04 => pub MESSAGE_ADDRESS_64_LOW<u32>);
    mmio_rw!(offset 0x08 => pub MESSAGE_ADDRESS_64_HIGH<u32>);
    mmio_rw!(offset 0x0c => pub MESSAGE_DATA_64<u32>);
    mmio_rw!(offset 0x10 => pub MASK_BITS_64<u32>);
    mmio_r!(offset 0x14 => pub PENDING_BITS_64<u32>);
}

#[derive(Debug)]
pub struct MSI {
    cap_ptr: usize,
    multiple_message_capable: MultipleMessage,
    per_vector_mask_capable: bool,
    bit64_address_capable: bool,
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
        let ctrl_cap = registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.read(cap_ptr);

        let multiple_message_capable = {
            let mlt_msg = (ctrl_cap >> 17) & 0b111;

            match mlt_msg {
                0b000 => MultipleMessage::One,
                0b001 => MultipleMessage::Two,
                0b010 => MultipleMessage::Four,
                0b011 => MultipleMessage::Eight,
                0b100 => MultipleMessage::Sixteen,
                0b101 => MultipleMessage::ThirtyTwo,
                _ => unreachable!(),
            }
        };

        let per_vector_mask_capable = ctrl_cap & registers::CTRL_PER_VECTOR_MASK_CAPABLE != 0;
        let bit64_address_capable = ctrl_cap & registers::CTRL_BIT64_ADDRESS_CAPABLE != 0;

        Self {
            cap_ptr,
            multiple_message_capable,
            per_vector_mask_capable,
            bit64_address_capable,
        }
    }

    /// Enable MSI.
    pub fn enable(&mut self) {
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.setbits(registers::CTRL_ENABLE, self.cap_ptr);
    }

    /// Disable MSI.
    pub fn disable(&mut self) {
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.clrbits(registers::CTRL_ENABLE, self.cap_ptr);
    }

    pub fn is_enabled(&self) -> bool {
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.read(self.cap_ptr) & registers::CTRL_ENABLE != 0
    }

    pub fn get_multiple_message_capable(&self) -> MultipleMessage {
        self.multiple_message_capable
    }

    pub fn set_multiple_message_enable(
        &mut self,
        mme: MultipleMessage,
    ) -> Result<(), &'static str> {
        if mme as u32 > self.multiple_message_capable as u32 {
            return Err("The number of interrupts is too large.");
        }

        let mme = match mme {
            MultipleMessage::One => 0b000,
            MultipleMessage::Two => 0b001,
            MultipleMessage::Four => 0b010,
            MultipleMessage::Eight => 0b011,
            MultipleMessage::Sixteen => 0b100,
            MultipleMessage::ThirtyTwo => 0b101,
        };

        let reg = registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.read(self.cap_ptr);
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.write(
            (reg & !(0b111 << (16 + 4))) | (mme << (16 + 4)),
            self.cap_ptr,
        );

        Ok(())
    }

    pub fn per_vector_mask_capable(&self) -> bool {
        self.per_vector_mask_capable
    }

    /// # Safety
    ///
    /// The address must be of an interrupt controller.
    pub unsafe fn set_message_address(&mut self, message_address: usize, message_data: u16) {
        if message_address > u32::MAX as usize {
            log::warn!("PCIe: Interrupt is not enabled because the address is too large.");
            return;
        }

        if self.bit64_address_capable {
            registers::MESSAGE_ADDRESS_64_LOW.write(message_address as u32, self.cap_ptr);
            registers::MESSAGE_ADDRESS_64_HIGH.write((message_address >> 32) as u32, self.cap_ptr);

            let data = registers::MESSAGE_DATA_64.read(self.cap_ptr);
            registers::MESSAGE_DATA_64.write(
                (data & 0xffff_0000) | (message_data & 0xffff) as u32,
                self.cap_ptr,
            );
        } else {
            registers::MESSAGE_ADDRESS_32.write(message_address as u32, self.cap_ptr);

            let data = registers::MESSAGE_DATA_32.read(self.cap_ptr);
            registers::MESSAGE_DATA_32.write(
                (data & 0xffff_0000) | (message_data & 0xffff) as u32,
                self.cap_ptr,
            );
        }
    }

    #[cfg(feature = "x86")]
    pub fn set_x86_interrupt(
        &mut self,
        apic_id: u32,
        vector: u16,
        edgetrigger: bool,
        deassert: bool,
    ) {
        let message_data = (vector & 0xFF)
            | if edgetrigger { 0 } else { 1 << 15 }
            | if deassert { 0 } else { 1 << 14 };
        let message_address = 0xfee0_0000 | ((apic_id & 0xff) << 12);

        unsafe { self.set_message_address(message_address as usize, message_data) };
    }

    pub fn set_mask(&mut self, mask: u32) {
        if !self.per_vector_mask_capable {
            return;
        }

        if self.bit64_address_capable {
            registers::MASK_BITS_64.write(mask, self.cap_ptr);
        } else {
            registers::MASK_BITS_32.write(mask, self.cap_ptr);
        }
    }

    pub fn read_peiding_bits(&self) -> Option<u32> {
        if !self.per_vector_mask_capable {
            return None;
        }

        if self.bit64_address_capable {
            Some(registers::PENDING_BITS_64.read(self.cap_ptr))
        } else {
            Some(registers::PENDING_BITS_32.read(self.cap_ptr))
        }
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
