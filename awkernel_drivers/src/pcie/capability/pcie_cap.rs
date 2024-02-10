use crate::pcie::{ConfigSpace, PCIeInfo};

pub mod registers {
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

    pub const _DEVICE_CAPABILITIES: usize = 0x04;
    pub const _DEVICE_STATUS_CONTROL: usize = 0x08;
    pub const _LINK_CAPABILITIES: usize = 0x0c;
    pub const LINK_STATUS_CONTROL: usize = 0x10;
    pub const _SLOT_CAPABILITIES: usize = 0x14;
    pub const _SLOT_STATUS_CONTROL: usize = 0x18;
    pub const _ROOT_CAPABILITY_CONTROL: usize = 0x1c;
    pub const _ROOT_STATUS: usize = 0x20;

    // Gen2 and later devices only
    pub const _DEVICE_CAPABILITIES_2: usize = 0x24;
    pub const _DEVICE_STATUS_CONTROL_2: usize = 0x28;
    pub const _LINK_CAPABILITIES_2: usize = 0x2c;
    pub const _LINK_STATUS_CONTROL_2: usize = 0x30;
    pub const _SLOT_CAPABILITIES_2: usize = 0x34;
    pub const _SLOT_STATUS_CONTROL_2: usize = 0x38;
}

#[derive(Debug)]
pub struct PCIeCap {
    cap_ptr: usize,
    config_space: ConfigSpace,
}

impl PCIeCap {
    pub fn new(info: &PCIeInfo, cap_ptr: usize) -> PCIeCap {
        PCIeCap {
            cap_ptr,
            config_space: info.config_space.clone(),
        }
    }

    pub fn get_link_status_control(&self) -> registers::LinkStatusControl {
        let reg = self
            .config_space
            .read_u32(self.cap_ptr + registers::LINK_STATUS_CONTROL);
        registers::LinkStatusControl::from_bits_truncate(reg)
    }

    pub fn set_link_status_control(&mut self, val: registers::LinkStatusControl) {
        self.config_space
            .write_u32(val.bits(), self.cap_ptr + registers::LINK_STATUS_CONTROL);
    }
}
