use super::{
    ixgbe_hw,
    ixgbe_operations::{self, start_hw_gen2, start_hw_generic, IxgbeOperations},
    ixgbe_regs::*,
    IxgbeDriverErr,
};
use crate::pcie::PCIeInfo;
use alloc::boxed::Box;
use awkernel_lib::delay::{wait_microsec, wait_millisec};
use ixgbe_hw::{EepromType, IxgbeEepromInfo, IxgbeHw, MediaType, PhyType, SfpType, SmartSpeed};

const IXGBE_82599_MAX_TX_QUEUES: u32 = 128;
const IXGBE_82599_MAX_RX_QUEUES: u32 = 128;
const IXGBE_82599_RAR_ENTRIES: u32 = 128;
const IXGBE_82599_MC_TBL_SIZE: u32 = 128;
const IXGBE_82599_VFT_TBL_SIZE: u32 = 128;
const IXGBE_82599_RX_PB_SIZE: u32 = 512;

pub struct Ixgbe82599;

impl Ixgbe82599 {
    fn new() -> Self {
        Self
    }
}

pub fn get_self() -> Box<dyn IxgbeOperations> {
    let ops = Ixgbe82599::new();

    Box::new(ops)
}

/// verify_fw_version_82599 - verify FW version for 82599
///  Verifies that installed the firmware version is 0.6 or higher
/// for SFI devices. All 82599 SFI devices should have version 0.6 or higher.
///  Returns IXGBE_ERR_EEPROM_VERSION if the FW is not present or
/// if the FW version is not supported.
fn verify_fw_version_82599<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    // firmware check is only necessary for SFI devices
    if hw.phy.media_type != MediaType::IxgbeMediaTypeFiber {
        return Ok(());
    }

    // get the offset to the Firmware Module block
    let mut fw_offset = [0; 1];
    if ops
        .eeprom_read(info, &mut hw.eeprom, IXGBE_FW_PTR, &mut fw_offset)
        .is_err()
    {
        log::error!("eeprom read at offset {} failed", IXGBE_FW_PTR);
        return Err(IxgbeDriverErr::EepromVersion);
    }

    if (fw_offset[0] == 0) || (fw_offset[0] == 0xFFFF) {
        return Err(IxgbeDriverErr::EepromVersion);
    }

    // get the offset to the Pass Through Patch Configuration block
    let mut fw_ptp_cfg_offset = [0; 1];
    if ops
        .eeprom_read(
            info,
            &mut hw.eeprom,
            fw_offset[0] + IXGBE_FW_PASSTHROUGH_PATCH_CONFIG_PTR,
            &mut fw_ptp_cfg_offset,
        )
        .is_err()
    {
        log::error!(
            "eeprom read at offset {} failed",
            fw_offset[0] + IXGBE_FW_PASSTHROUGH_PATCH_CONFIG_PTR
        );
        return Err(IxgbeDriverErr::EepromVersion);
    }

    if (fw_ptp_cfg_offset[0] == 0) || (fw_ptp_cfg_offset[0] == 0xFFFF) {
        return Err(IxgbeDriverErr::EepromVersion);
    }

    // get the firmware version
    let mut fw_version = [0; 1];
    if ops
        .eeprom_read(
            info,
            &mut hw.eeprom,
            fw_ptp_cfg_offset[0] + IXGBE_FW_PATCH_VERSION_4,
            &mut fw_version,
        )
        .is_err()
    {
        log::error!(
            "eeprom read at offset {} failed",
            fw_ptp_cfg_offset[0] + IXGBE_FW_PATCH_VERSION_4
        );
        return Err(IxgbeDriverErr::EepromVersion);
    }

    if fw_version[0] > 0x5 {
        return Ok(());
    }

    Err(IxgbeDriverErr::EepromVersion)
}

/// verify_lesm_fw_enabled_82599 - Checks LESM FW module state.
/// Returns TRUE if the LESM FW module is present and enabled. Otherwise
/// returns FALSE. Smart Speed must be disabled if LESM FW module is enabled.
fn verify_lesm_fw_enabled_82599<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<bool, IxgbeDriverErr> {
    // get the offset to the Firmware Module block
    let mut fw_offset = [0; 1];
    ops.eeprom_read(info, &mut hw.eeprom, IXGBE_FW_PTR, &mut fw_offset)?;

    if (fw_offset[0] == 0) || (fw_offset[0] == 0xFFFF) {
        return Ok(false);
    }

    // get the offset to the LESM Parameters block
    let mut fw_lesm_param_offset = [0; 1];
    ops.eeprom_read(
        info,
        &mut hw.eeprom,
        fw_offset[0] + IXGBE_FW_LESM_PARAMETERS_PTR,
        &mut fw_lesm_param_offset,
    )?;

    if (fw_lesm_param_offset[0] == 0) || (fw_lesm_param_offset[0] == 0xFFFF) {
        return Ok(false);
    }

    // get the LESM state word
    let mut fw_lesm_state = [0; 1];
    ops.eeprom_read(
        info,
        &mut hw.eeprom,
        fw_lesm_param_offset[0] + IXGBE_FW_LESM_STATE_1,
        &mut fw_lesm_state,
    )?;

    if fw_lesm_state[0] & IXGBE_FW_LESM_STATE_ENABLED != 0 {
        return Ok(true);
    }

    Ok(false)
}

/// reset_pipeline_82599 - perform pipeline reset
/// Reset pipeline by asserting Restart_AN together with LMS change to ensure
/// full pipeline reset.  This function assumes the SW/FW lock is held.
fn reset_pipeline_82599(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    // Enable link if disabled in NVM
    let mut autoc2_reg = ixgbe_hw::read_reg(info, IXGBE_AUTOC2)?;
    if autoc2_reg & IXGBE_AUTOC2_LINK_DISABLE_MASK != 0 {
        autoc2_reg &= !IXGBE_AUTOC2_LINK_DISABLE_MASK;
        ixgbe_hw::write_reg(info, IXGBE_AUTOC2, autoc2_reg)?;
        ixgbe_hw::write_flush(info)?;
    }

    let mut autoc_reg = ixgbe_hw::read_reg(info, IXGBE_AUTOC)?;
    autoc_reg |= IXGBE_AUTOC_AN_RESTART;
    // Write AUTOC register with toggled LMS[2] bit and Restart_AN
    ixgbe_hw::write_reg(
        info,
        IXGBE_AUTOC,
        autoc_reg ^ (0x4 << IXGBE_AUTOC_LMS_SHIFT),
    )?;
    // Wait for AN to leave state 0
    let mut anlp1_reg = 0;
    for _ in 0..10 {
        wait_millisec(4);
        anlp1_reg = ixgbe_hw::read_reg(info, IXGBE_ANLP1)?;
        if anlp1_reg & IXGBE_ANLP1_AN_STATE_MASK != 0 {
            break;
        }
    }

    // Write AUTOC register with original LMS field and Restart_AN
    ixgbe_hw::write_reg(info, IXGBE_AUTOC, autoc_reg)?;
    ixgbe_hw::write_flush(info)?;

    if anlp1_reg & IXGBE_ANLP1_AN_STATE_MASK == 0 {
        log::debug!("auto negotiation not completed\n");
        return Err(IxgbeDriverErr::ResetFailed);
    }

    Ok(())
}

/// get_link_capabilities_82599 - Determines link capabilities
/// Determines the link capabilities by reading the AUTOC register.
fn get_link_capabilities_82599(
    info: &PCIeInfo,
    hw: &IxgbeHw,
) -> Result<(u32, bool), IxgbeDriverErr> {
    use SfpType::*;

    // Check if 1G SFP module.
    match hw.phy.sfp_type {
        IxgbeSfpType1gCuCore0
        | IxgbeSfpType1gCuCore1
        | IxgbeSfpType1gLxCore0
        | IxgbeSfpType1gLxCore1
        | IxgbeSfpType1gSxCore0
        | IxgbeSfpType1gSxCore1 => return Ok((IXGBE_LINK_SPEED_1GB_FULL, true)),
        _ => (),
    };

    // Determine link capabilities based on the stored value of AUTOC,
    // which represents EEPROM defaults.  If AUTOC value has not
    // been stored, use the current register values.
    let autoc = if hw.mac.orig_link_settings_stored {
        hw.mac.orig_autoc
    } else {
        ixgbe_hw::read_reg(info, IXGBE_AUTOC)?
    };

    let (mut speed, mut autoneg) = match autoc & IXGBE_AUTOC_LMS_MASK {
        IXGBE_AUTOC_LMS_1G_LINK_NO_AN => (IXGBE_LINK_SPEED_1GB_FULL, false),
        IXGBE_AUTOC_LMS_10G_LINK_NO_AN => (IXGBE_LINK_SPEED_10GB_FULL, false),
        IXGBE_AUTOC_LMS_1G_AN => (IXGBE_LINK_SPEED_1GB_FULL, true),
        IXGBE_AUTOC_LMS_10G_SERIAL => (IXGBE_LINK_SPEED_10GB_FULL, false),
        IXGBE_AUTOC_LMS_KX4_KX_KR | IXGBE_AUTOC_LMS_KX4_KX_KR_1G_AN => {
            let mut speed_temp = IXGBE_LINK_SPEED_UNKNOWN;
            if autoc & IXGBE_AUTOC_KR_SUPP != 0 {
                speed_temp |= IXGBE_LINK_SPEED_10GB_FULL;
            }
            if autoc & IXGBE_AUTOC_KX4_SUPP != 0 {
                speed_temp |= IXGBE_LINK_SPEED_10GB_FULL;
            }
            if autoc & IXGBE_AUTOC_KX_SUPP != 0 {
                speed_temp |= IXGBE_LINK_SPEED_1GB_FULL;
            }
            (speed_temp, true)
        }
        IXGBE_AUTOC_LMS_KX4_KX_KR_SGMII => {
            let mut speed_temp = IXGBE_LINK_SPEED_100_FULL;
            if autoc & IXGBE_AUTOC_KR_SUPP != 0 {
                speed_temp |= IXGBE_LINK_SPEED_10GB_FULL;
            }
            if autoc & IXGBE_AUTOC_KX4_SUPP != 0 {
                speed_temp |= IXGBE_LINK_SPEED_10GB_FULL;
            }
            if autoc & IXGBE_AUTOC_KX_SUPP != 0 {
                speed_temp |= IXGBE_LINK_SPEED_1GB_FULL;
            }
            (speed_temp, true)
        }
        IXGBE_AUTOC_LMS_SGMII_1G_100M => {
            (IXGBE_LINK_SPEED_1GB_FULL | IXGBE_LINK_SPEED_100_FULL, false)
        }
        _ => return Err(IxgbeDriverErr::LinkSetup),
    };

    if hw.phy.multispeed_fiber {
        speed |= IXGBE_LINK_SPEED_10GB_FULL | IXGBE_LINK_SPEED_1GB_FULL;

        //  QSFP must not enable full auto-negotiation
        // Limited autoneg is enabled at 1G
        autoneg = hw.phy.media_type != MediaType::IxgbeMediaTypeFiberQsfp;
    }

    Ok((speed, autoneg))
}

/// set_hard_rate_select_speed - Set module link speed
/// Set module link speed via RS0/RS1 rate select pins.
fn set_hard_rate_select_speed(info: &PCIeInfo, speed: u32) -> Result<(), IxgbeDriverErr> {
    let mut esdp_reg = ixgbe_hw::read_reg(info, IXGBE_ESDP)?;

    esdp_reg = match speed {
        IXGBE_LINK_SPEED_10GB_FULL => esdp_reg | (IXGBE_ESDP_SDP5_DIR | IXGBE_ESDP_SDP5),
        IXGBE_LINK_SPEED_1GB_FULL => {
            esdp_reg &= !IXGBE_ESDP_SDP5;
            esdp_reg | IXGBE_ESDP_SDP5_DIR
        }
        _ => {
            log::debug!("Invalid fixed module speed\n");
            return Ok(());
        }
    };

    ixgbe_hw::write_reg(info, IXGBE_ESDP, esdp_reg)?;
    ixgbe_hw::write_flush(info)?;

    Ok(())
}

/// phy_setup_phy_link_tnx - Set and restart auto-neg
///  // Restart auto-negotiation and PHY and waits for completion.
fn phy_setup_phy_link_tnx<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
) -> Result<(), IxgbeDriverErr> {
    let (speed, _autoneg) = ixgbe_operations::get_copper_link_capabilities(ops, info, hw)?;

    if speed & IXGBE_LINK_SPEED_10GB_FULL != 0 {
        // Set or unset auto-negotiation 10G advertisement
        let mut autoneg_reg = ops.phy_read_reg(
            info,
            hw,
            IXGBE_MII_10GBASE_T_AUTONEG_CTRL_REG,
            IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
        )?;

        autoneg_reg &= !IXGBE_MII_10GBASE_T_ADVERTISE;
        if hw.phy.autoneg_advertised & IXGBE_LINK_SPEED_10GB_FULL != 0 {
            autoneg_reg |= IXGBE_MII_10GBASE_T_ADVERTISE;
        }

        ops.phy_write_reg(
            info,
            hw,
            IXGBE_MII_10GBASE_T_AUTONEG_CTRL_REG,
            IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
            autoneg_reg,
        )?;
    }

    if speed & IXGBE_LINK_SPEED_1GB_FULL != 0 {
        // Set or unset auto-negotiation 1G advertisement
        let mut autoneg_reg = ops.phy_read_reg(
            info,
            hw,
            IXGBE_MII_AUTONEG_XNP_TX_REG,
            IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
        )?;

        autoneg_reg &= !IXGBE_MII_1GBASE_T_ADVERTISE_XNP_TX;
        if hw.phy.autoneg_advertised & IXGBE_LINK_SPEED_1GB_FULL != 0 {
            autoneg_reg |= IXGBE_MII_1GBASE_T_ADVERTISE_XNP_TX;
        }

        ops.phy_write_reg(
            info,
            hw,
            IXGBE_MII_AUTONEG_XNP_TX_REG,
            IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
            autoneg_reg,
        )?;
    }

    if speed & IXGBE_LINK_SPEED_100_FULL != 0 {
        // Set or unset auto-negotiation 100M advertisement
        let mut autoneg_reg = ops.phy_read_reg(
            info,
            hw,
            IXGBE_MII_AUTONEG_ADVERTISE_REG,
            IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
        )?;

        autoneg_reg &= !IXGBE_MII_100BASE_T_ADVERTISE;
        if hw.phy.autoneg_advertised & IXGBE_LINK_SPEED_100_FULL != 0 {
            autoneg_reg |= IXGBE_MII_100BASE_T_ADVERTISE;
        }

        ops.phy_write_reg(
            info,
            hw,
            IXGBE_MII_AUTONEG_ADVERTISE_REG,
            IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
            autoneg_reg,
        )?;
    }

    // Blocked by MNG FW so don't reset PHY
    if ixgbe_operations::check_reset_blocked(info, hw)? {
        return Ok(());
    }

    // Restart PHY auto-negotiation.
    let mut autoneg_reg = ops.phy_read_reg(
        info,
        hw,
        IXGBE_MDIO_AUTO_NEG_CONTROL,
        IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
    )?;

    autoneg_reg |= IXGBE_MII_RESTART;

    ops.phy_write_reg(
        info,
        hw,
        IXGBE_MDIO_AUTO_NEG_CONTROL,
        IXGBE_MDIO_AUTO_NEG_DEV_TYPE,
        autoneg_reg,
    )?;

    Ok(())
}

/// read_i2c_byte_82599 - Reads 8 bit word over I2C
/// Performs byte read operation to SFP module's EEPROM over I2C interface at
/// a specified device address.
pub fn read_i2c_byte_82599<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &IxgbeHw,
    byte_offset: u8,
    dev_addr: u8,
) -> Result<u8, IxgbeDriverErr> {
    if hw.phy.qsfp_shared_i2c_bus {
        // Acquire I2C bus ownership.
        let mut esdp = ixgbe_hw::read_reg(info, IXGBE_ESDP)?;
        esdp |= IXGBE_ESDP_SDP0;
        ixgbe_hw::write_reg(info, IXGBE_ESDP, esdp)?;
        ixgbe_hw::write_flush(info)?;

        let mut timeout = 200;
        while timeout > 0 {
            esdp = ixgbe_hw::read_reg(info, IXGBE_ESDP)?;
            if esdp & IXGBE_ESDP_SDP1 != 0 {
                break;
            }

            wait_millisec(5);
            timeout -= 1;
        }

        if timeout == 0 {
            log::debug!("Driver can't access resource, acquiring I2C bus timeout.\n");
            esdp = ixgbe_hw::read_reg(info, IXGBE_ESDP)?;
            esdp &= !IXGBE_ESDP_SDP0;
            ixgbe_hw::write_reg(info, IXGBE_ESDP, esdp)?;
            ixgbe_hw::write_flush(info)?;
            return Err(IxgbeDriverErr::I2c);
        }
    }

    let data =
        ixgbe_operations::read_i2c_byte_generic_int(ops, info, hw, byte_offset, dev_addr, true)?;

    if hw.phy.qsfp_shared_i2c_bus {
        // Release I2C bus ownership.
        let mut esdp = ixgbe_hw::read_reg(info, IXGBE_ESDP)?;
        esdp &= !IXGBE_ESDP_SDP0;
        ixgbe_hw::write_reg(info, IXGBE_ESDP, esdp)?;
        ixgbe_hw::write_flush(info)?;
    }

    Ok(data)
}

/// write_i2c_byte_82599 - Writes 8 bit word over I2C
///  Performs byte write operation to SFP module's EEPROM over I2C interface at
/// a specified device address.
fn write_i2c_byte_82599<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &IxgbeHw,
    byte_offset: u8,
    dev_addr: u8,
    data: u8,
) -> Result<(), IxgbeDriverErr> {
    let mut timeout = 200;

    let mut esdp;
    if hw.phy.qsfp_shared_i2c_bus {
        // Acquire I2C bus ownership.
        esdp = ixgbe_hw::read_reg(info, IXGBE_ESDP)?;
        esdp |= IXGBE_ESDP_SDP0;
        ixgbe_hw::write_reg(info, IXGBE_ESDP, esdp)?;
        ixgbe_hw::write_flush(info)?;

        while timeout > 0 {
            esdp = ixgbe_hw::read_reg(info, IXGBE_ESDP)?;
            if esdp & IXGBE_ESDP_SDP1 != 0 {
                break;
            }

            wait_millisec(5);
            timeout -= 1;
        }

        if timeout == 0 {
            log::debug!("Driver can't access resource, acquiring I2C bus timeout.\n");
            if hw.phy.qsfp_shared_i2c_bus {
                // Release I2C bus ownership.
                esdp = ixgbe_hw::read_reg(info, IXGBE_ESDP)?;
                esdp &= !IXGBE_ESDP_SDP0;
                ixgbe_hw::write_reg(info, IXGBE_ESDP, esdp)?;
                ixgbe_hw::write_flush(info)?;
            }
            return Err(IxgbeDriverErr::I2c);
        }
    }

    ixgbe_operations::write_i2c_byte_generic_int(ops, info, hw, byte_offset, dev_addr, data, true)?;

    if hw.phy.qsfp_shared_i2c_bus {
        // Release I2C bus ownership.
        esdp = ixgbe_hw::read_reg(info, IXGBE_ESDP)?;
        esdp &= !IXGBE_ESDP_SDP0;
        ixgbe_hw::write_reg(info, IXGBE_ESDP, esdp)?;
        ixgbe_hw::write_flush(info)?;
    }

    Ok(())
}

/// setup_mac_link_smartspeed - Set MAC link speed using SmartSpeed
///  Implements the Intel SmartSpeed algorithm.
fn setup_mac_link_smartspeed<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
    speed: u32,
    autoneg_wait_to_complete: bool,
) -> Result<(), IxgbeDriverErr> {
    fn error_out(link_up: bool, link_speed: u32, e: IxgbeDriverErr) -> Result<(), IxgbeDriverErr> {
        if link_up && (link_speed == IXGBE_LINK_SPEED_1GB_FULL) {
            log::debug!("Smartspeed has downgraded the link speed from the maximum advertised\n");
        }
        Err(e)
    }

    let link_speed = IXGBE_LINK_SPEED_UNKNOWN;
    let link_up = false;
    let autoc_reg = ixgbe_hw::read_reg(info, IXGBE_AUTOC)?;

    // Set autoneg_advertised value based on input link speed
    hw.phy.autoneg_advertised = 0;

    if speed & IXGBE_LINK_SPEED_10GB_FULL != 0 {
        hw.phy.autoneg_advertised |= IXGBE_LINK_SPEED_10GB_FULL;
    }

    if speed & IXGBE_LINK_SPEED_1GB_FULL != 0 {
        hw.phy.autoneg_advertised |= IXGBE_LINK_SPEED_1GB_FULL;
    }

    if speed & IXGBE_LINK_SPEED_100_FULL != 0 {
        hw.phy.autoneg_advertised |= IXGBE_LINK_SPEED_100_FULL;
    }

    // Implement Intel SmartSpeed algorithm.  SmartSpeed will reduce the
    // autoneg advertisement if link is unable to be established at the
    // highest negotiated rate.  This can sometimes happen due to integrity
    // issues with the physical media connection.

    // First, try to get link with full advertisement
    hw.phy.smart_speed_active = false;
    for _ in 0..IXGBE_SMARTSPEED_MAX_RETRIES {
        if let Err(e) = setup_mac_link_82599(ops, info, hw, speed, autoneg_wait_to_complete) {
            return error_out(link_up, link_speed, e);
        }

        // Wait for the controller to acquire link.  Per IEEE 802.3ap,
        // Section 73.10.2, we may have to wait up to 500ms if KR is
        // attempted, or 200ms if KX/KX4/BX/BX4 is attempted, per
        // Table 9 in the AN MAS.
        for _ in 0..5 {
            wait_millisec(100);

            // If we have link, just jump out
            let (link_speed, link_up) = match ops.mac_check_link(info, hw, false) {
                Ok(pair) => pair,
                Err(e) => {
                    return error_out(link_up, link_speed, e);
                }
            };

            if link_up {
                if link_speed == IXGBE_LINK_SPEED_1GB_FULL {
                    log::debug!(
                        "Smartspeed has downgraded the link speed from the maximum advertised\n"
                    );
                }
                return Ok(());
            }
        }
    }

    // We didn't get link.  If we advertised KR plus one of KX4/KX
    // (or BX4/BX), then disable KR and try again.
    if (((autoc_reg & IXGBE_AUTOC_KR_SUPP) == 0)
        || ((autoc_reg & IXGBE_AUTOC_KX4_KX_SUPP_MASK) == 0))
        && link_up
        && (link_speed == IXGBE_LINK_SPEED_1GB_FULL)
    {
        log::debug!("Smartspeed has downgraded the link speed from the maximum advertised\n");
    }

    // Turn SmartSpeed on to disable KR support
    hw.phy.smart_speed_active = true;
    if let Err(e) = setup_mac_link_82599(ops, info, hw, speed, autoneg_wait_to_complete) {
        return error_out(link_up, link_speed, e);
    }

    // Wait for the controller to acquire link.  600ms will allow for
    // the AN link_fail_inhibit_timer as well for multiple cycles of
    // parallel detect, both 10g and 1g. This allows for the maximum
    // connect attempts as defined in the AN MAS table 73-7.
    for _ in 0..6 {
        wait_millisec(100);

        // If we have link, just jump out
        if let Err(e) = ops.mac_check_link(info, hw, false) {
            return error_out(link_up, link_speed, e);
        }

        if link_up && (link_speed == IXGBE_LINK_SPEED_1GB_FULL) {
            log::debug!("Smartspeed has downgraded the link speed from the maximum advertised\n");
        }
    }

    // We didn't get link.  Turn SmartSpeed back off.
    hw.phy.smart_speed_active = false;
    if let Err(e) = setup_mac_link_82599(ops, info, hw, speed, autoneg_wait_to_complete) {
        return error_out(link_up, link_speed, e);
    }

    if link_up && (link_speed == IXGBE_LINK_SPEED_1GB_FULL) {
        log::debug!("Smartspeed has downgraded the link speed from the maximum advertised\n");
    }

    Ok(())
}

/// setup_mac_link_82599 - Set MAC link speed
/// Set the link speed in the AUTOC register and restarts link.
fn setup_mac_link_82599<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
    mut speed: u32,
    autoneg_wait_to_complete: bool,
) -> Result<(), IxgbeDriverErr> {
    // Check to see if speed passed in is supported.
    let (link_capabilities, autoneg) = ops.mac_get_link_capabilities(info, hw)?;

    speed &= link_capabilities;

    if speed == IXGBE_LINK_SPEED_UNKNOWN {
        return Err(IxgbeDriverErr::LinkSetup);
    }

    // holds the value of AUTOC register at this current point in time
    let current_autoc = ixgbe_hw::read_reg(info, IXGBE_AUTOC)?;
    // holds the cached value of AUTOC register
    // Temporary variable used for comparison purposes
    let mut autoc = current_autoc;

    // Use stored value (EEPROM defaults) of AUTOC to find KR/KX4 support
    let orig_autoc = if hw.mac.orig_link_settings_stored {
        hw.mac.orig_autoc
    } else {
        autoc
    };

    let link_mode = autoc & IXGBE_AUTOC_LMS_MASK;
    let pma_pmd_1g = autoc & IXGBE_AUTOC_1G_PMA_PMD_MASK;
    let autoc2 = ixgbe_hw::read_reg(info, IXGBE_AUTOC2)?;
    let pma_pmd_10g_serial = autoc2 & IXGBE_AUTOC2_10G_SERIAL_PMA_PMD_MASK;
    if link_mode == IXGBE_AUTOC_LMS_KX4_KX_KR
        || link_mode == IXGBE_AUTOC_LMS_KX4_KX_KR_1G_AN
        || link_mode == IXGBE_AUTOC_LMS_KX4_KX_KR_SGMII
    {
        // Set KX4/KX/KR support according to speed requested
        autoc &= !(IXGBE_AUTOC_KX4_KX_SUPP_MASK | IXGBE_AUTOC_KR_SUPP);
        if speed & IXGBE_LINK_SPEED_10GB_FULL != 0 {
            if orig_autoc & IXGBE_AUTOC_KX4_SUPP != 0 {
                autoc |= IXGBE_AUTOC_KX4_SUPP;
            }
            if (orig_autoc & IXGBE_AUTOC_KR_SUPP != 0) && !hw.phy.smart_speed_active {
                autoc |= IXGBE_AUTOC_KR_SUPP;
            }
        }
        if speed & IXGBE_LINK_SPEED_1GB_FULL != 0 {
            autoc |= IXGBE_AUTOC_KX_SUPP;
        }
    } else if (pma_pmd_1g == IXGBE_AUTOC_1G_SFI)
        && (link_mode == IXGBE_AUTOC_LMS_1G_LINK_NO_AN || link_mode == IXGBE_AUTOC_LMS_1G_AN)
    {
        // Switch from 1G SFI to 10G SFI if requested
        if (speed == IXGBE_LINK_SPEED_10GB_FULL) && (pma_pmd_10g_serial == IXGBE_AUTOC2_10G_SFI) {
            autoc &= !IXGBE_AUTOC_LMS_MASK;
            autoc |= IXGBE_AUTOC_LMS_10G_SERIAL;
        }
    } else if (pma_pmd_10g_serial == IXGBE_AUTOC2_10G_SFI)
        && (link_mode == IXGBE_AUTOC_LMS_10G_SERIAL)
    {
        // Switch from 10G SFI to 1G SFI if requested
        if (speed == IXGBE_LINK_SPEED_1GB_FULL) && (pma_pmd_1g == IXGBE_AUTOC_1G_SFI) {
            autoc &= !IXGBE_AUTOC_LMS_MASK;
            if autoneg || hw.phy.phy_type == PhyType::IxgbePhyQsfpIntel {
                autoc |= IXGBE_AUTOC_LMS_1G_AN;
            } else {
                autoc |= IXGBE_AUTOC_LMS_1G_LINK_NO_AN;
            }
        }
    }

    let mut status = Ok(());
    if autoc != current_autoc {
        // Restart link
        ops.mac_prot_autoc_write(info, hw, autoc)?;

        // Only poll for autoneg to complete if specified to do so
        if autoneg_wait_to_complete
            && (link_mode == IXGBE_AUTOC_LMS_KX4_KX_KR
                || link_mode == IXGBE_AUTOC_LMS_KX4_KX_KR_1G_AN
                || link_mode == IXGBE_AUTOC_LMS_KX4_KX_KR_SGMII)
        {
            let mut links_reg = 0; // Just in case Autoneg time=0
            for _ in 0..IXGBE_AUTO_NEG_TIME {
                links_reg = ixgbe_hw::read_reg(info, IXGBE_LINKS)?;
                if links_reg & IXGBE_LINKS_KX_AN_COMP != 0 {
                    break;
                }
                wait_millisec(100);
            }
            if links_reg & IXGBE_LINKS_KX_AN_COMP == 0 {
                status = Err(IxgbeDriverErr::AutonegNotComplete);
                log::debug!("Autoneg did not complete.\n");
            }
        }

        // Add delay to filter out noises during initial link setup
        wait_millisec(50);
    }

    status
}

/// setup_copper_link_82599 - Set the PHY autoneg advertised field
/// Restarts link on PHY and MAC based on settings passed in.
fn setup_copper_link_82599<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
    speed: u32,
    autoneg_wait_to_complete: bool,
) -> Result<(), IxgbeDriverErr> {
    log::debug!("ixgbe_setup_copper_link_82599");

    // Setup the PHY according to input speed
    ops.phy_setup_link_speed(info, hw, speed, autoneg_wait_to_complete)?;
    // Set up MAC
    start_mac_link_82599(ops, info, hw, autoneg_wait_to_complete)?;

    Ok(())
}

/// start_mac_link_82599 - Setup MAC link settings
/// Configures link settings based on values in the ixgbe_hw struct.
/// Restarts the link.  Performs autonegotiation if needed.
fn start_mac_link_82599<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    hw: &mut IxgbeHw,
    autoneg_wait_to_complete: bool,
) -> Result<(), IxgbeDriverErr> {
    // reset_pipeline requires us to hold this lock as it writes to
    // AUTOC.
    let mut got_lock = false;
    if verify_lesm_fw_enabled_82599(ops, info, hw)? {
        ops.mac_acquire_swfw_sync(info, IXGBE_GSSR_MAC_CSR_SM)?;
        got_lock = true;
    }

    // Restart link
    let ret = reset_pipeline_82599(info);
    if got_lock {
        ops.mac_release_swfw_sync(info, IXGBE_GSSR_MAC_CSR_SM)?;
    }
    ret?;

    // Only poll for autoneg to complete if specified to do so
    let mut status = Ok(());
    if autoneg_wait_to_complete {
        let autoc_reg = ixgbe_hw::read_reg(info, IXGBE_AUTOC)?;
        if (autoc_reg & IXGBE_AUTOC_LMS_MASK) == IXGBE_AUTOC_LMS_KX4_KX_KR
            || (autoc_reg & IXGBE_AUTOC_LMS_MASK) == IXGBE_AUTOC_LMS_KX4_KX_KR_1G_AN
            || (autoc_reg & IXGBE_AUTOC_LMS_MASK) == IXGBE_AUTOC_LMS_KX4_KX_KR_SGMII
        {
            let mut links_reg = 0; // Just in case Autoneg time = 0
            for _ in 0..IXGBE_AUTO_NEG_TIME {
                links_reg = ixgbe_hw::read_reg(info, IXGBE_LINKS)?;
                if links_reg & IXGBE_LINKS_KX_AN_COMP != 0 {
                    break;
                }
                wait_millisec(100);
            }
            if links_reg & IXGBE_LINKS_KX_AN_COMP == 0 {
                status = Err(IxgbeDriverErr::AutonegNotComplete);
                log::debug!("Autoneg did not complete.\n");
            }
        }
    }

    // Add delay to filter out noises during initial link setup
    wait_millisec(50);

    status
}

impl IxgbeOperations for Ixgbe82599 {
    // MAC Operations

    /// mac_reset_hw - Perform hardware reset
    /// Resets the hardware by resetting the transmit and receive units, masks
    /// and clears all interrupts, perform a PHY reset, and perform a link (MAC)
    /// reset.
    fn mac_reset_hw(&self, info: &mut PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        // Call adapter stop to disable tx/rx and clear interrupts
        self.mac_stop_adapter(info, hw)?;

        // flush pending Tx transactions
        ixgbe_operations::clear_tx_pending(info, hw)?;

        self.phy_init(info, hw)?;

        // Setup SFP module if there is one present.
        if hw.phy.sfp_setup_needed {
            self.mac_setup_sfp(info, hw)?;
            hw.phy.sfp_setup_needed = false;
        }

        // Reset PHY
        if !hw.phy.no_reset {
            self.phy_reset(info, hw)?;
        }

        // remember AUTOC from before we reset
        let curr_lms = ixgbe_hw::read_reg(info, IXGBE_AUTOC)? & IXGBE_AUTOC_LMS_MASK;

        let mut status = Ok(());

        // Double resets are required for recovery from certain error
        // conditions.  Between resets, it is necessary to stall to
        // allow time for any pending HW events to complete.
        let count = if hw.mac.flags & IXGBE_FLAGS_DOUBLE_RESET_REQUIRED != 0 {
            2
        } else {
            1
        };

        for _ in 0..count {
            // Issue global reset to the MAC.  Needs to be SW reset if link is up.
            // If link reset is used when link is up, it might reset the PHY when
            // mng is using it.  If link is down or the flag to force full link
            // reset is set, then perform link reset.
            let mut ctrl = IXGBE_CTRL_LNK_RST;
            let (_link_speed, link_up) = self.mac_check_link(info, hw, false)?;
            if link_up {
                ctrl = IXGBE_CTRL_RST;
            }

            ctrl |= ixgbe_hw::read_reg(info, IXGBE_CTRL)?;
            ixgbe_hw::write_reg(info, IXGBE_CTRL, ctrl)?;
            ixgbe_hw::write_flush(info)?;

            // Poll for reset bit to self-clear meaning reset is complete
            for _ in 0..10 {
                wait_microsec(1);
                ctrl = ixgbe_hw::read_reg(info, IXGBE_CTRL)?;
                if ctrl & IXGBE_CTRL_RST_MASK == 0 {
                    break;
                }
            }

            if ctrl & IXGBE_CTRL_RST_MASK != 0 {
                status = Err(IxgbeDriverErr::ResetFailed);
                log::debug!("Reset polling failed to complete.\n");
            }

            wait_millisec(50);
        }

        // Store the original AUTOC/AUTOC2 values if they have not been
        // stored off yet.  Otherwise restore the stored original
        // values since the reset operation sets back to defaults.
        let autoc = ixgbe_hw::read_reg(info, IXGBE_AUTOC)?;
        let mut autoc2 = ixgbe_hw::read_reg(info, IXGBE_AUTOC2)?;

        // Enable link if disabled in NVM
        if autoc2 & IXGBE_AUTOC2_LINK_DISABLE_MASK != 0 {
            autoc2 &= !IXGBE_AUTOC2_LINK_DISABLE_MASK;
            ixgbe_hw::write_reg(info, IXGBE_AUTOC2, autoc2)?;
            ixgbe_hw::write_flush(info)?;
        }

        if !hw.mac.orig_link_settings_stored {
            hw.mac.orig_autoc = autoc;
            hw.mac.orig_autoc2 = autoc2;
            hw.mac.orig_link_settings_stored = true;
        } else {
            //  If MNG FW is running on a multi-speed device that
            // doesn't autoneg with out driver support we need to
            // leave LMS in the state it was before we MAC reset.
            // Likewise if we support WoL we don't want change the
            // LMS state.
            if hw.phy.multispeed_fiber && ixgbe_operations::mng_enabled(info, hw)? {
                hw.mac.orig_autoc = (hw.mac.orig_autoc & !IXGBE_AUTOC_LMS_MASK) | curr_lms;
            }

            if autoc != hw.mac.orig_autoc {
                self.mac_prot_autoc_write(info, hw, hw.mac.orig_autoc)?;
            }

            if (autoc2 & IXGBE_AUTOC2_UPPER_MASK) != (hw.mac.orig_autoc2 & IXGBE_AUTOC2_UPPER_MASK)
            {
                autoc2 &= !IXGBE_AUTOC2_UPPER_MASK;
                autoc2 |= hw.mac.orig_autoc2 & IXGBE_AUTOC2_UPPER_MASK;
                ixgbe_hw::write_reg(info, IXGBE_AUTOC2, autoc2)?;
            }
        }

        // Store the permanent mac address
        self.mac_get_mac_addr(info, &mut hw.mac.perm_addr)?;

        // Store MAC address from RAR0, clear receive address registers, and
        // clear the multicast table.  Also reset num_rar_entries to 128,
        // since we modify this value when programming the SAN MAC address.
        hw.mac.num_rar_entries = 128;
        self.mac_init_rx_addrs(info, hw)?;

        status
    }

    /// mac_start_hw - Prepare hardware for Tx/Rx
    /// Starts the hardware using the generic start_hw function
    /// and the generation start_hw function.
    /// Then performs revision-specific operations, if any.
    fn mac_start_hw(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        start_hw_generic(self, info, hw)?;
        start_hw_gen2(info, hw)?;

        // We need to run link autotry after the driver loads */
        hw.mac.autotry_restart = true;

        verify_fw_version_82599(self, info, hw)
    }

    /// mac_get_media_type - Get media type
    /// // Returns the media type (fiber, copper, backplane)
    fn mac_get_media_type(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> MediaType {
        use MediaType::*;
        use PhyType::*;

        // Detect if there is a copper PHY attached.
        match hw.phy.phy_type {
            IxgbePhyCuUnknown | IxgbePhyTn => {
                return IxgbeMediaTypeCopper;
            }
            _ => (),
        }

        match info.get_id() {
            IXGBE_DEV_ID_82599_KX4
            | IXGBE_DEV_ID_82599_KX4_MEZZ
            | IXGBE_DEV_ID_82599_COMBO_BACKPLANE
            | IXGBE_DEV_ID_82599_KR
            | IXGBE_DEV_ID_82599_BACKPLANE_FCOE
            | IXGBE_DEV_ID_82599_XAUI_LOM => IxgbeMediaTypeBackplane, // Default device ID is mezzanine card KX/KX4
            IXGBE_DEV_ID_82599_SFP
            | IXGBE_DEV_ID_82599_SFP_FCOE
            | IXGBE_DEV_ID_82599_SFP_EM
            | IXGBE_DEV_ID_82599_SFP_SF2
            | IXGBE_DEV_ID_82599_SFP_SF_QP
            | IXGBE_DEV_ID_82599EN_SFP => IxgbeMediaTypeFiber,
            IXGBE_DEV_ID_82599_CX4 => IxgbeMediaTypeCx4,
            IXGBE_DEV_ID_82599_T3_LOM => IxgbeMediaTypeCopper,
            IXGBE_DEV_ID_82599_QSFP_SF_QP => IxgbeMediaTypeFiberQsfp,
            IXGBE_DEV_ID_82599_BYPASS => {
                hw.phy.multispeed_fiber = true;
                IxgbeMediaTypeFiberFixed
            }
            _ => IxgbeMediaTypeUnknown,
        }
    }

    /// prot_autoc_write - Hides MAC differences needed for AUTOC write
    /// This part (82599) may need to hold the SW/FW lock around all writes to
    /// AUTOC. Likewise after a write we need to do a pipeline reset.
    fn mac_prot_autoc_write(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
        autoc: u32,
    ) -> Result<(), IxgbeDriverErr> {
        // Blocked by MNG FW so bail
        if ixgbe_operations::check_reset_blocked(info, hw)? {
            return Ok(());
        }

        // We only need to get the lock if:
        // - We didn't do it already (in the read part of a read-modify-write)
        // - LESM is enabled.
        let mut locked = false;
        if verify_lesm_fw_enabled_82599(self, info, hw)? {
            self.mac_acquire_swfw_sync(info, IXGBE_GSSR_MAC_CSR_SM)?;
            locked = true;
        }

        let ret_write_reg = ixgbe_hw::write_reg(info, IXGBE_AUTOC, autoc);
        let reset_pipeline = reset_pipeline_82599(info);

        // Free the SW/FW semaphore as we either grabbed it here.
        if locked {
            self.mac_release_swfw_sync(info, IXGBE_GSSR_MAC_CSR_SM)?;
        }

        ret_write_reg?;
        reset_pipeline?;

        Ok(())
    }

    fn mac_setup_link(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
        speed: u32,
        autoneg_wait_to_complete: bool,
    ) -> Result<(), IxgbeDriverErr> {
        use MediaType::*;
        use SmartSpeed::*;

        // This is based on OpenBSD ixgbe_init_phy_ops_82599() and ixgbe_setup_sfp_modules_82599()
        // https://github.com/openbsd/src/blob/90c8c6adfa2b8abd1dc328444ad22b9090325b9d/sys/dev/pci/ixgbe_82599.c#L151
        let media_type = self.mac_get_media_type(info, hw);
        if media_type == IxgbeMediaTypeCopper {
            setup_copper_link_82599(self, info, hw, speed, autoneg_wait_to_complete)?;
        } else {
            // Refers to ixgbe_init_mac_link_ops_82599()
            if hw.phy.multispeed_fiber {
                ixgbe_operations::setup_mac_link_multispeed_fiber(
                    self,
                    info,
                    hw,
                    speed,
                    autoneg_wait_to_complete,
                )?;
            } else if (media_type == IxgbeMediaTypeBackplane)
                && (hw.phy.smart_speed == IxgbeSmartSpeedAuto
                    || hw.phy.smart_speed == IxgbeSmartSpeedOn)
                && !verify_lesm_fw_enabled_82599(self, info, hw)?
            {
                setup_mac_link_smartspeed(self, info, hw, speed, autoneg_wait_to_complete)?;
            } else {
                setup_mac_link_82599(self, info, hw, speed, autoneg_wait_to_complete)?;
            }
        }

        Ok(())
    }

    fn mac_setup_mac_link(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
        speed: u32,
        autoneg_wait_to_complete: bool,
    ) -> Result<(), IxgbeDriverErr> {
        if hw.phy.multispeed_fiber {
            setup_mac_link_82599(self, info, hw, speed, autoneg_wait_to_complete)
        } else {
            Err(IxgbeDriverErr::NotImplemented)
        }
    }

    fn mac_setup_sfp(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        if hw.phy.sfp_type != SfpType::IxgbeSfpTypeUnknown {
            // ixgbe_init_mac_link_ops_82599(hw);

            hw.phy.no_reset = true;

            let (_list_offset, mut data_offset) =
                ixgbe_operations::get_sfp_init_sequence_offsets(self, info, hw)?;

            // PHY config will finish before releasing the semaphore
            ixgbe_operations::mac_swfw_sync_mut(
                self,
                info,
                IXGBE_GSSR_MAC_CSR_SM,
                hw.eeprom.semaphore_delay,
                || {
                    let mut data_value = [0; 1];
                    data_offset += 1;
                    self.eeprom_read(info, &mut hw.eeprom, data_offset, &mut data_value)?;

                    while data_value[0] != 0xffff {
                        ixgbe_hw::write_reg(info, IXGBE_CORECTL, data_value[0] as u32)?;
                        ixgbe_hw::write_flush(info)?;
                        data_offset += 1;
                        self.eeprom_read(info, &mut hw.eeprom, data_offset, &mut data_value)?;
                    }
                    Ok(())
                },
            )?;

            // Restart DSP and set SFI mode
            if self
                .mac_prot_autoc_write(info, hw, hw.mac.orig_autoc | IXGBE_AUTOC_LMS_10G_SERIAL)
                .is_err()
            {
                log::debug!("sfp module setup not complete\n");
                return Err(IxgbeDriverErr::SfpSetupNotComplete);
            }
        }

        Ok(())
    }

    fn mac_get_link_capabilities(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
    ) -> Result<(u32, bool), IxgbeDriverErr> {
        if self.mac_get_media_type(info, hw) == MediaType::IxgbeMediaTypeCopper {
            ixgbe_operations::get_copper_link_capabilities(self, info, hw)
        } else {
            get_link_capabilities_82599(info, hw)
        }
    }

    fn mac_set_rate_select_speed(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
        speed: u32,
    ) -> Result<(), IxgbeDriverErr> {
        if hw.phy.multispeed_fiber {
            if self.mac_get_media_type(info, hw) == MediaType::IxgbeMediaTypeFiberFixed {
                ixgbe_operations::set_soft_rate_select_speed(self, info, hw, speed)
            } else {
                set_hard_rate_select_speed(info, speed)
            }
        } else {
            log::error!("mac_set_rate_select_speed: Not Implemented");
            Err(IxgbeDriverErr::NotImplemented)
        }
    }

    fn phy_init(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        if info.get_id() == IXGBE_DEV_ID_82599_QSFP_SF_QP {
            // Store flag indicating I2C bus access control unit.
            hw.phy.qsfp_shared_i2c_bus = true;

            // Initialize access to QSFP+ I2C bus
            let mut esdp = ixgbe_hw::read_reg(info, IXGBE_ESDP)?;
            esdp |= IXGBE_ESDP_SDP0_DIR;
            esdp &= !IXGBE_ESDP_SDP1_DIR;
            esdp &= !IXGBE_ESDP_SDP0;
            esdp &= !IXGBE_ESDP_SDP0_NATIVE;
            esdp &= !IXGBE_ESDP_SDP1_NATIVE;
            ixgbe_hw::write_reg(info, IXGBE_ESDP, esdp)?;
            ixgbe_hw::write_flush(info)?;
        }
        // Identify the PHY or SFP module
        self.phy_identify(info, hw)?;

        if hw.phy.sfp_type != SfpType::IxgbeSfpTypeUnknown {
            hw.phy.no_reset = true;
        }

        Ok(())
    }

    /// identify_phy - Get physical layer module
    /// Determines the physical layer module found on the current adapter.
    /// If PHY already detected, maintains current PHY type in hw struct,
    /// otherwise executes the PHY detection routine.
    fn phy_identify(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        // Detect PHY if not unknown - returns success if already detected.
        let mut status = ixgbe_operations::phy_identify_phy_generic(self, info, hw);
        if status.is_err() {
            // 82599 10GBASE-T requires an external PHY
            if self.mac_get_media_type(info, hw) == MediaType::IxgbeMediaTypeCopper {
                return Ok(());
            } else {
                status = ixgbe_operations::phy_identify_module_generic(self, info, hw);
            }
        }

        // Set PHY type none if no PHY detected
        if hw.phy.phy_type == PhyType::IxgbePhyUnknown {
            hw.phy.phy_type = PhyType::IxgbePhyNone;
            return Ok(());
        }

        // Return error if SFP module has been detected but is not supported
        if hw.phy.phy_type == PhyType::IxgbePhySfpUnsupported {
            return Err(IxgbeDriverErr::SfpNotSupported);
        }

        status
    }

    fn phy_setup_link(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        match hw.phy.phy_type {
            PhyType::IxgbePhyTn => phy_setup_phy_link_tnx(self, info, hw),
            _ => ixgbe_operations::phy_setup_link_generic(self, info, hw),
        }
    }

    fn phy_read_i2c_byte(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        byte_offset: u8,
        dev_addr: u8,
    ) -> Result<u8, IxgbeDriverErr> {
        if info.get_id() == IXGBE_DEV_ID_82599_QSFP_SF_QP {
            read_i2c_byte_82599(self, info, hw, byte_offset, dev_addr)
        } else {
            ixgbe_operations::read_i2c_byte_generic_int(self, info, hw, byte_offset, dev_addr, true)
        }
    }

    fn phy_write_i2c_byte(
        &self,
        info: &PCIeInfo,
        hw: &IxgbeHw,
        byte_offset: u8,
        dev_addr: u8,
        data: u8,
    ) -> Result<(), IxgbeDriverErr> {
        if info.get_id() == IXGBE_DEV_ID_82599_QSFP_SF_QP {
            write_i2c_byte_82599(self, info, hw, byte_offset, dev_addr, data)
        } else {
            ixgbe_operations::write_i2c_byte_generic_int(
                self,
                info,
                hw,
                byte_offset,
                dev_addr,
                data,
                true,
            )
        }
    }

    fn eeprom_read(
        &self,
        info: &PCIeInfo,
        eeprom: &mut IxgbeEepromInfo,
        offset: u16,
        data: &mut [u16],
    ) -> Result<(), IxgbeDriverErr> {
        // If EEPROM is detected and can be addressed using 14 bits,
        // use EERD otherwise use bit bang
        if eeprom.eeprom_type == EepromType::IxgbeEepromSpi && offset as u32 <= IXGBE_EERD_MAX_ADDR
        {
            ixgbe_operations::read_eerd_buffer_generic(self, info, eeprom, offset, 1, data)
        } else {
            ixgbe_operations::read_eeprom_bit_bang_generic(self, info, eeprom, offset, data)
        }
    }
}

/// Return `(mcft_size: u32, vft_size: u32, num_rar_entries: u32,
/// rx_pb_size: u32, max_rx_queues: u32, max_tx_queues: u32,
/// max_msix_vectors: u16, arc_subsystem_valid: bool)`.
#[allow(clippy::type_complexity)]
pub fn set_mac_val(
    info: &PCIeInfo,
) -> Result<(u32, u32, u32, u32, u32, u32, u16, bool), IxgbeDriverErr> {
    let fwsm_offset = get_fwsm_offset(info.get_id())?;
    let arc_subsystem_valid = (ixgbe_hw::read_reg(info, fwsm_offset)? & IXGBE_FWSM_MODE_MASK) != 0;

    Ok((
        IXGBE_82599_MC_TBL_SIZE,
        IXGBE_82599_VFT_TBL_SIZE,
        IXGBE_82599_RAR_ENTRIES,
        IXGBE_82599_RX_PB_SIZE,
        IXGBE_82599_MAX_RX_QUEUES,
        IXGBE_82599_MAX_TX_QUEUES,
        0,
        arc_subsystem_valid,
    ))
}
