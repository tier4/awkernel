//! # genet: Broadcom's Genet Ethernet controller.

use core::f32::consts::E;

use awkernel_lib::{
    addr::{virt_addr::VirtAddr, Addr},
    net::ether::ETHER_ADDR_LEN,
};

mod registers {
    use awkernel_lib::mmio_r;

    pub const REV_MAJOR_V5: u8 = 6;
    pub const SYS_RBUF_FLUSH_RESET: u32 = 1 << 1;

    mmio_r!(offset 0x000 => pub SYS_REV_CTRL<u32>);
    mmio_r!(offset 0x008 => pub SYS_RBUF_FLUSH_CTRL<u32>);

    mmio_r!(offset 0x80c => pub UMAC_MAC0<u32>);
    mmio_r!(offset 0x810 => pub UMAC_MAC1<u32>);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GenetError {
    InvalidMajorVersion,
    InvalidMacAddress,
}

pub fn attach(
    base_addr: VirtAddr,
    irqs: &[u16],
    phy_mode: &str,
    mac_addr: &Option<[u8; ETHER_ADDR_LEN]>,
) -> Result<(), GenetError> {
    // Check the major version of the Genet controller.
    let (major_ver, minor_ver) = get_version(base_addr);

    if major_ver != registers::REV_MAJOR_V5 {
        log::error!("GENET: unsupported major version {major_ver}");
        return Err(GenetError::InvalidMajorVersion);
    }

    log::debug!("GENET: major_ver = {major_ver}, minor_ver = {minor_ver}");

    // Get the MAC address.
    let mac_addr = if let Some(mac_addr) = mac_addr {
        mac_addr.clone()
    } else {
        read_mac_addr(base_addr)
    };

    if mac_addr.iter().all(|&b| b == 0) {
        log::error!("GENET: invalid MAC address");
        return Err(GenetError::InvalidMacAddress);
    }

    log::debug!(
        "GENET: mac_addr = {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
        mac_addr[0],
        mac_addr[1],
        mac_addr[2],
        mac_addr[3],
        mac_addr[4],
        mac_addr[5]
    );

    Ok(())
}

fn get_version(base_addr: VirtAddr) -> (u8, u8) {
    let sys_rev_ctrl = registers::SYS_REV_CTRL.read(base_addr.as_usize());

    (
        ((sys_rev_ctrl >> 24) & 0b1111) as u8,
        ((sys_rev_ctrl >> 16) & 0b1111) as u8,
    )
}

fn read_mac_addr(base_addr: VirtAddr) -> [u8; 6] {
    let maclo = registers::UMAC_MAC0.read(base_addr.as_usize());
    let machi = registers::UMAC_MAC1.read(base_addr.as_usize());

    [
        ((maclo >> 24) & 0xff) as u8,
        ((maclo >> 16) & 0xff) as u8,
        ((maclo >> 8) & 0xff) as u8,
        (maclo & 0xff) as u8,
        ((machi >> 8) & 0xff) as u8,
        (machi & 0xff) as u8,
    ]
}
