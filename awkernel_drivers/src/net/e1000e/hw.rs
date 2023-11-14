use crate::pcie::DeviceInfo;

pub struct E1000EHw {
    mac_type: MacType,
}

#[derive(Debug)]
enum MacType {
    EmUndefined = 0,
    Em82542Rev20,
    Em82542Rev21,
    Em82543,
    Em82544,
    Em82540,
    Em82545,
    Em82545Rev3,
    EmIcpXxxx,
    Em82546,
    Em82546Rev3,
    Em82541,
    Em82541Rev2,
    Em82547,
    Em82547Rev2,
    Em82571,
    Em82572,
    Em82573,
    Em82574,
    Em82575,
    Em82576,
    Em82580,
    EmI350,
    EmI210,
    Em80003es2lan,
    EmIch8lan,
    EmIch9lan,
    EmIch10lan,
    EmPchlan,
    EmPch2lan,
    EmPchLpt,
    EmPchSpt,
    EmPchCnp,
    EmPchTgp,
    EmPchAdp,
    EmNumMacs,
}

/// https://github.com/openbsd/src/blob/f058c8dbc8e3b2524b639ac291b898c7cc708996/sys/dev/pci/if_em_hw.c#L403
fn get_mac_type(device: u16) -> MacType {
    use crate::pcie::pcie_id::*;

    match device {
        INTEL_82574GBE_DEVICE_ID => MacType::Em82574,
        INTEL_I219_LM3_DEVICE_ID => MacType::EmPchLpt,
        _ => unreachable!(),
    }
}

impl E1000EHw {
    pub fn new(info: &DeviceInfo) -> Self {
        let mac_type = get_mac_type(info.get_id());
        Self { mac_type }
    }

    /// https://github.com/openbsd/src/blob/f058c8dbc8e3b2524b639ac291b898c7cc708996/sys/dev/pci/if_em_hw.c#L1559
    pub fn init_hw(info: &DeviceInfo) {
        todo!();
    }
}
