use awkernel_lib::interrupt::IRQ;

use alloc::{borrow::Cow, boxed::Box};

use crate::pcie::{ConfigSpace, PCIeDeviceErr, PCIeInfo};

mod registers {
    pub const MESSAGE_CONTROL_NEXT_PTR_CAP_ID: usize = 0x00;

    // Message Control Register
    pub const CTRL_ENABLE: u32 = 1 << 16;
    pub const CTRL_BIT64_ADDRESS_CAPABLE: u32 = 1 << (7 + 16);
    pub const CTRL_PER_VECTOR_MASK_CAPABLE: u32 = 1 << (8 + 16);

    pub const MESSAGE_ADDRESS_32: usize = 0x04;
    pub const MESSAGE_DATA_32: usize = 0x08;
    pub const MASK_BITS_32: usize = 0x0c;
    pub const PENDING_BITS_32: usize = 0x10;

    pub const MESSAGE_ADDRESS_64_LOW: usize = 0x04;
    pub const MESSAGE_ADDRESS_64_HIGH: usize = 0x08;
    pub const MESSAGE_DATA_64: usize = 0x0c;
    pub const MASK_BITS_64: usize = 0x10;
    pub const PENDING_BITS_64: usize = 0x14;
}

#[derive(Debug)]
pub struct Msi {
    cap_ptr: usize,
    config_space: ConfigSpace,
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
impl Msi {
    pub fn new(info: &PCIeInfo, cap_ptr: usize) -> Self {
        let config_space = info.config_space.clone();

        let ctrl_cap = config_space.read_u32(cap_ptr + registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID);

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
            config_space,
            multiple_message_capable,
            per_vector_mask_capable,
            bit64_address_capable,
        }
    }

    /// Enable MSI.
    pub fn enable(&mut self) {
        let reg = self
            .config_space
            .read_u32(self.cap_ptr + registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID);
        self.config_space.write_u32(
            reg | registers::CTRL_ENABLE,
            self.cap_ptr + registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID,
        )
    }

    /// Disable MSI.
    pub fn disable(&mut self) {
        let reg = self
            .config_space
            .read_u32(self.cap_ptr + registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID);
        self.config_space.write_u32(
            reg & !registers::CTRL_ENABLE,
            self.cap_ptr + registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID,
        )
    }

    pub fn is_enabled(&self) -> bool {
        self.config_space
            .read_u32(self.cap_ptr + registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID)
            & registers::CTRL_ENABLE
            != 0
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

        let reg = self
            .config_space
            .read_u32(self.cap_ptr + registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID);
        self.config_space.write_u32(
            (reg & !(0b111 << (16 + 4))) | (mme << (16 + 4)),
            self.cap_ptr + registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID,
        );

        Ok(())
    }

    pub fn per_vector_mask_capable(&self) -> bool {
        self.per_vector_mask_capable
    }

    pub fn register_handler<F>(
        &mut self,
        name: Cow<'static, str>,
        func: Box<F>,
        segment_number: usize,
        target: u32,
    ) -> Result<IRQ, PCIeDeviceErr>
    where
        F: Fn(u16) + Send + 'static,
    {
        let mut message_data = 0;
        let mut message_address = 0;
        let mut message_address_upper = 0;

        let upper = if self.bit64_address_capable {
            Some(&mut message_address_upper)
        } else {
            None
        };

        let irq = awkernel_lib::interrupt::register_handler_pcie_msi(
            name,
            func,
            segment_number,
            target,
            &mut message_data,
            &mut message_address,
            upper,
        )
        .or(Err(PCIeDeviceErr::Interrupt))?;

        if self.bit64_address_capable {
            self.config_space
                .write_u32(message_data, self.cap_ptr + registers::MESSAGE_DATA_64);
            self.config_space.write_u32(
                message_address,
                self.cap_ptr + registers::MESSAGE_ADDRESS_64_LOW,
            );
            self.config_space.write_u32(
                message_address_upper,
                self.cap_ptr + registers::MESSAGE_ADDRESS_64_HIGH,
            );
        } else {
            self.config_space
                .write_u32(message_data, self.cap_ptr + registers::MESSAGE_DATA_32);
            self.config_space.write_u32(
                message_address,
                self.cap_ptr + registers::MESSAGE_ADDRESS_32,
            );
        }

        Ok(irq)
    }

    pub fn set_mask(&mut self, mask: u32) {
        if !self.per_vector_mask_capable {
            return;
        }

        if self.bit64_address_capable {
            self.config_space
                .write_u32(mask, self.cap_ptr + registers::MASK_BITS_64);
        } else {
            self.config_space
                .write_u32(mask, self.cap_ptr + registers::MASK_BITS_32);
        }
    }

    pub fn read_pending_bits(&self) -> Option<u32> {
        if !self.per_vector_mask_capable {
            return None;
        }

        if self.bit64_address_capable {
            Some(
                self.config_space
                    .read_u32(self.cap_ptr + registers::PENDING_BITS_64),
            )
        } else {
            Some(
                self.config_space
                    .read_u32(self.cap_ptr + registers::PENDING_BITS_32),
            )
        }
    }
}
