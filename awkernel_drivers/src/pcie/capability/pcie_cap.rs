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
        pub struct DeviceStatusControl2:u32{
            //Device Status2 Register
            const DEVICE_STATUS2 = 0xffff0000;
            // Device Control2 Register
            const END_END_TLP_PREFIX_BLOCKING = 1 << 15;
            const OBFF_EN = 0x6000;
            const LTR_EN = 1 << 10;
            const IDO_COMPLETION_ENABLE = 1 << 9;
            const IDO_REQUEST_ENABLE = 1 << 8;
            const ARI_FORWARDING_EN = 1 << 5;
            const CPL_TIMEOUT_DIS = 1 << 4;
            const CPL_TIMEOUT_VALUE = 0xf;
        }
        pub struct DeviceStatusControl: u32 {
            //Device Status Register
            const TRANSACTIONS_PEND = 1 << 21;
            const AUX_PWR = 1 << 20;
            const USR_DETECTED = 1 << 19;
            const FATAL_ERR = 1 << 18;
            const NON_FATAL_ERR = 1 << 17;
            const STATUS_CORR_ERR = 1 << 16;
            // Device Control Register
            const INITIATE_FLR = 1 << 15;
            const MAX_READ_REQUEST_SIZE = 0x7 << 12;  // 3 bits starting at bit 12
            const NO_SNOOP_EN = 1 << 11;
            const AUX_POWER_PM_EN = 1 << 10;
            const PHANTOM_FUNC_EN = 1 << 9;
            const EXTENDED_TAG_EN = 1 << 8;
            const MAX_PAYLOAD_SIZE = 0x7 << 5;  // 3 bits starting at bit 5
            const RELAXED_ORD_EN = 1 << 4;
            const USR_REPORT_EN = 1 << 3;
            const FATAL_ERR_EN = 1 << 2;
            const NON_FATAL_ERR_EN = 1 << 1;
            const CTRL_CORR_ERR_EN = 1 << 0;
        }

    }

    pub const _DEVICE_CAPABILITIES: usize = 0x04;
    pub const DEVICE_STATUS_CONTROL: usize = 0x08;
    pub const _LINK_CAPABILITIES: usize = 0x0c;
    pub const LINK_STATUS_CONTROL: usize = 0x10;
    pub const _SLOT_CAPABILITIES: usize = 0x14;
    pub const _SLOT_STATUS_CONTROL: usize = 0x18;
    pub const _ROOT_CAPABILITY_CONTROL: usize = 0x1c;
    pub const _ROOT_STATUS: usize = 0x20;

    // Gen2 and later devices only
    pub const _DEVICE_CAPABILITIES_2: usize = 0x24;
    pub const DEVICE_STATUS_CONTROL_2: usize = 0x28;
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

    pub fn get_device_status_control2(&self) -> registers::DeviceStatusControl2 {
        let reg = self
            .config_space
            .read_u32(self.cap_ptr + registers::DEVICE_STATUS_CONTROL_2);
        registers::DeviceStatusControl2::from_bits_truncate(reg)
    }

    pub fn set_device_status_control2(&self, val: registers::DeviceStatusControl2) {
        self.config_space.write_u32(
            val.bits(),
            self.cap_ptr + registers::DEVICE_STATUS_CONTROL_2,
        );
    }

    pub fn get_device_status_control(&self) -> registers::DeviceStatusControl {
        let reg = self
            .config_space
            .read_u32(self.cap_ptr + registers::DEVICE_STATUS_CONTROL);
        registers::DeviceStatusControl::from_bits_truncate(reg)
    }

    pub fn set_device_status_control(&self, val: registers::DeviceStatusControl) {
        self.config_space
            .write_u32(val.bits(), self.cap_ptr + registers::DEVICE_STATUS_CONTROL);
    }
}
