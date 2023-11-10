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

pub struct MSI {
    cap_ptr: usize,
}

pub enum MSIMultipleMessage {
    One = 1,
    Two = 2,
    Four = 4,
    Eight = 8,
    Sixteen = 16,
    ThirtyTwo = 32,
}

/// # Message Signaled Interrupts (MSI)
///
/// ## Multiple Message Enable (MME)
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
///
/// 0b0100_1001_1010_0000
impl MSI {
    pub fn new(cap_ptr: usize) -> Self {
        Self { cap_ptr }
    }
}
