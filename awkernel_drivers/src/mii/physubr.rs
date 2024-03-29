use super::*;

pub fn dev_attach(
    mii: &mut dyn Mii,
    mii_data: &mut MiiData,
    flags: MiiFlags,
    phy: &mut dyn MiiPhy,
) -> Result<(), MiiError> {
    let phy_data = phy.get_phy_data_mut();

    phy_data.flags |= flags;

    phy.reset(mii, mii_data)?;

    // TODO:

    Ok(())
}

pub fn reset(mii: &mut dyn Mii, mii_data: &MiiData, phy: &mut dyn MiiPhy) -> Result<(), MiiError> {
    let phy_data = phy.get_phy_data();

    let mut reg = if phy_data.flags.contains(MiiFlags::NOISOLATE) {
        BMCR_RESET
    } else {
        BMCR_RESET | BMCR_ISO
    };

    mii.write_reg(phy_data.phy, MII_BMCR, reg)?;

    // Wait 100ms for it to complete.
    for _ in 0..100 {
        reg = mii.read_reg(phy_data.phy, MII_BMCR)?;

        if (reg & BMCR_RESET) == 0 {
            break;
        }
        awkernel_lib::delay::wait_microsec(1000);
    }

    // NB: a PHY may default to being powered down and/or isolated.
    reg &= !(BMCR_PDOWN | BMCR_ISO);

    if !phy_data.flags.contains(MiiFlags::NOISOLATE) {
        if let Some(ife) = mii_data.media.get_current() {
            if ife.get_instance() != phy_data.inst {
                reg |= BMCR_ISO;
            }
        } else if phy_data.inst != 0 {
            reg |= BMCR_ISO;
        }
    }

    if mii.read_reg(phy_data.phy, MII_BMCR)? != reg {
        mii.write_reg(phy_data.phy, MII_BMCR, reg)?;
    }

    Ok(())
}
