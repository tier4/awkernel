use awkernel_drivers::raspi5::raspi5_pcie_bridge;

const PCIE_BASE: usize = 0x1000120000;

pub fn init_pcie_bridge() {
    let pcie_host_bridge = raspi5_pcie_bridge::CBcmPCIeHostBridge { m_base: PCIE_BASE };
    awkernel_lib::delay::wait_microsec(100000);
    let _init_status = unsafe { pcie_host_bridge.pcie_init() };

    awkernel_lib::delay::wait_microsec(100000);
    let _bridge_status = pcie_host_bridge.enable_bridge();
    awkernel_lib::delay::wait_microsec(100000);
    awkernel_lib::delay::wait_microsec(100000);
    let _device_status = pcie_host_bridge.enable_device(0x20000, 0, 0);
    awkernel_lib::delay::wait_microsec(100000);
}
