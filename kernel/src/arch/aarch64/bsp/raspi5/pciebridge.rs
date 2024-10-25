use awkernel_drivers::raspi5::raspi5_pcie_bridge;

const PCIE_BASE: usize = 0x1000120000;

pub fn init_pcie_bridge() {
    let pcie_host_bridge = raspi5_pcie_bridge::CBcmPCIeHostBridge { m_base: PCIE_BASE };
    awkernel_lib::delay::wait_microsec(100000);
    let _init_status = unsafe { pcie_host_bridge.pcie_init() };
}
