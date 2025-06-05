#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PCIeClass {
    Unclassified,
    MassStorageController,
    NetworkController,
    DisplayController,
    MultimediaController,
    MemoryController,
    BridgeDevice(PCIeBridgeSubClass),
    SimpleCommunicationController,
    BaseSystemPeripheral,
    InputDeviceController,
    DockingStation,
    Processor,
    SerialBusController,
    WirelessController,
    IntelligentController,
    SatelliteCommunicationController,
    EncryptionController,
    SignalProcessingController,
    ProcessingAccelerator,
    NonEssentialInstrumentation,
    Coprocessor,
    UnassignedClass,
}

impl PCIeClass {
    pub fn from_u8(pcie_class: u8, pcie_sub_class: u8) -> Option<Self> {
        let pcie_class = match pcie_class {
            0x00 => Self::Unclassified,
            0x01 => Self::MassStorageController,
            0x02 => Self::NetworkController,
            0x03 => Self::DisplayController,
            0x04 => Self::MultimediaController,
            0x05 => Self::MemoryController,
            0x06 => Self::BridgeDevice(PCIeBridgeSubClass::from_u8(pcie_sub_class)?),
            0x07 => Self::SimpleCommunicationController,
            0x08 => Self::BaseSystemPeripheral,
            0x09 => Self::InputDeviceController,
            0x0a => Self::DockingStation,
            0x0b => Self::Processor,
            0x0c => Self::SerialBusController,
            0x0d => Self::WirelessController,
            0x0e => Self::IntelligentController,
            0x0f => Self::SatelliteCommunicationController,
            0x10 => Self::EncryptionController,
            0x11 => Self::SignalProcessingController,
            0x12 => Self::ProcessingAccelerator,
            0x13 => Self::NonEssentialInstrumentation,
            0x40 => Self::Coprocessor,
            0xff => Self::UnassignedClass,
            _ => return None,
        };

        Some(pcie_class)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PCIeBridgeSubClass {
    HostBridge = 0,
    ISA = 1,
    EISA = 2,
    MCA = 3,
    PCItoPCI = 4,
    PCMCIA = 5,
    NuBus = 6,
    CardBus = 7,
    RACEway = 8,
    PCItoPCIsemisync = 9,
    InfiniBandToPCIhost = 0xa,
    Other = 0x80,
}

impl PCIeBridgeSubClass {
    pub fn from_u8(pcie_sub_class: u8) -> Option<Self> {
        let pcie_sub_class = match pcie_sub_class {
            0x00 => Self::HostBridge,
            0x01 => Self::ISA,
            0x02 => Self::EISA,
            0x03 => Self::MCA,
            0x04 => Self::PCItoPCI,
            0x05 => Self::PCMCIA,
            0x06 => Self::NuBus,
            0x07 => Self::CardBus,
            0x08 => Self::RACEway,
            0x09 => Self::PCItoPCIsemisync,
            0x0a => Self::InfiniBandToPCIhost,
            0x80 => Self::Other,
            _ => return None,
        };

        Some(pcie_sub_class)
    }
}
