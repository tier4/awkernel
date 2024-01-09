pub mod registers {
    use awkernel_lib::mmio_rw;
    use bitflags::bitflags;

    bitflags! {
        pub struct LinkStatusControl:u32 {
            // Link Status Register
            const LINK_AUTONOMOUS_BANDWIDTH_STATUS = 1 << 31;
            const LINK_BANDWIDTH_MANAGEMENT_STATUS = 1 << 30;
            const DATA_LINK_LAYER_LINK_ACTIVE = 1 << 29;
            const SLOT_CLOCK_CONFIG = 1 << 28;
            const LINK_TRAINING = 1 << 27;

            // Link Control Register
            const LINK_AUTONOMOUS_BANDWIDTH_INTERRUPT_ENABLE = 1 << 11;
            const LINK_BANDWIDTH_MANAGEMENT_INTERRUPT_ENABLE = 1 << 10;
            const HARDWARE_AUTONOMOUS_WIDTH_DISABLE = 1 << 9;
            const ENABLE_CLOCK_POWER_MANAGEMENT = 1 << 8;
            const EXTENDED_SYNCH = 1 << 7;
            const COMMON_CLOCK_CONFIGURATION = 1 << 6;
            const RETAIN_LINK = 1 << 5;
            const LINK_DISABLE = 1 << 4;
            const READ_COMPLETION_BOUNDARY_CONTROL = 1 << 3;
            const ASPM_L1 = 1 << 1;
            const ASPM_L0S = 1;
        }
    }

    mmio_rw!(offset 0x00 => pub PCIE_CAPABILITIES_NEXT_PTR_CAP_ID<u32>);

    mmio_rw!(offset 0x04 => pub DEVICE_CAPABILITIES<u32>);
    mmio_rw!(offset 0x08 => pub DEVICE_STATUS_CONTROL<u32>);
    mmio_rw!(offset 0x0c => pub LINK_CAPABILITIES<u32>);
    mmio_rw!(offset 0x10 => pub LINK_STATUS_CONTROL<LinkStatusControl>);
    mmio_rw!(offset 0x14 => pub SLOT_CAPABILITIES<u32>);
    mmio_rw!(offset 0x18 => pub SLOT_STATUS_CONTROL<u32>);
    mmio_rw!(offset 0x1c => pub ROOT_CAPABILITY_CONTROL<u32>);
    mmio_rw!(offset 0x20 => pub ROOT_STATUS<u32>);

    // Gen2 and later devices only
    mmio_rw!(offset 0x24 => pub DEVICE_CAPABILITIES_2<u32>);
    mmio_rw!(offset 0x28 => pub DEVICE_STATUS_CONTROL_2<u32>);
    mmio_rw!(offset 0x2c => pub LINK_CAPABILITIES_2<u32>);
    mmio_rw!(offset 0x30 => pub LINK_STATUS_CONTROL_2<LinkStatusControl>);
    mmio_rw!(offset 0x34 => pub SLOT_CAPABILITIES_2<u32>);
    mmio_rw!(offset 0x38 => pub SLOT_STATUS_CONTROL_2<u32>);
}

#[derive(Debug)]
pub struct PCIeCap {
    cap_ptr: usize,
}

impl PCIeCap {
    pub fn new(cap_ptr: usize) -> PCIeCap {
        PCIeCap { cap_ptr }
    }

    pub fn get_link_status_control(&self) -> registers::LinkStatusControl {
        registers::LINK_STATUS_CONTROL.read(self.cap_ptr)
    }

    pub fn set_link_status_control(&mut self, val: registers::LinkStatusControl) {
        registers::LINK_STATUS_CONTROL.write(val, self.cap_ptr);
    }
}
