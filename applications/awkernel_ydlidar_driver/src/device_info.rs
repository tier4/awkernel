pub struct DeviceInfo {
    pub model_number: u8,
    pub firmware_major_version: u8,
    pub firmware_minor_version: u8,
    pub hardware_version: u8,
    pub serial_number: [u8; 16],
}
