use super::{
    ixgbe_hw,
    ixgbe_operations::{self, IxgbeOperations},
    ixgbe_regs::*,
    ixgbe_x540, IxgbeDriverErr,
};
use crate::pcie::PCIeInfo;
use alloc::boxed::Box;
use ixgbe_hw::{EepromType, IxgbeEepromInfo, IxgbeHw, MediaType};
use ixgbe_operations::get_copper_link_capabilities;

const IXGBE_X540_MAX_TX_QUEUES: u32 = 128;
const IXGBE_X540_MAX_RX_QUEUES: u32 = 128;
const IXGBE_X540_RAR_ENTRIES: u32 = 128;
const IXGBE_X540_MC_TBL_SIZE: u32 = 128;
const IXGBE_X540_VFT_TBL_SIZE: u32 = 128;
const IXGBE_X540_RX_PB_SIZE: u32 = 384;

pub struct IxgbeX550;

impl IxgbeX550 {
    fn new() -> Self {
        Self
    }
}

pub fn get_self() -> Box<dyn IxgbeOperations> {
    let ops = IxgbeX550::new();

    Box::new(ops)
}

fn read_ee_hostif_buffer_x550<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    offset: u16,
    mut words: u16,
    data: &mut [u16],
) -> Result<(), IxgbeDriverErr> {
    let mask = IXGBE_GSSR_SW_MNG_SM | IXGBE_GSSR_EEP_SM;

    ixgbe_operations::mac_swfw_sync_mut(ops, info, mask, 0, || {
        let mut words_to_read;
        let mut current_word = 0;
        while words > 0 {
            if words > FW_MAX_READ_BUFFER_SIZE / 2 {
                words_to_read = FW_MAX_READ_BUFFER_SIZE / 2;
            } else {
                words_to_read = words;
            }

            let buffer = IxgbeHicReadShadowRam {
                hdr: IxgbeHicHdr2 {
                    req: IxgbeHicHdr2Req {
                        cmd: FW_READ_SHADOW_RAM_CMD,
                        buf_lenh: 0,
                        buf_lenl: FW_READ_SHADOW_RAM_LEN,
                        checksum: FW_DEFAULT_CHECKSUM,
                    },
                },
                // convert offset from words to bytes
                address: u32::to_be((offset + current_word) as u32 * 2),
                length: u16::to_be(words_to_read * 2),
                pad2: 0,
                data: 0,
                pad3: 0,
            };

            let ptr = &buffer as *const IxgbeHicReadShadowRam as *const u32;
            let size_in_u32 =
                core::mem::size_of::<IxgbeHicReadShadowRam>() / core::mem::size_of::<u32>();
            let slice = unsafe { core::slice::from_raw_parts(ptr, size_in_u32) };
            if let Err(e) = ixgbe_operations::hic_unlocked(
                info,
                slice,
                core::mem::size_of::<IxgbeHicReadShadowRam>() as u32,
                IXGBE_HI_COMMAND_TIMEOUT,
            ) {
                log::debug!("Host interface command failed");
                return Err(e);
            }

            let mut i = 0;
            while i < words_to_read {
                let reg = IXGBE_FLEX_MNG + (FW_NVM_DATA_OFFSET << 2) + 2 * i as usize;
                let mut value = ixgbe_hw::read_reg(info, reg)?;

                data[current_word as usize] = (value & 0xffff) as u16;
                //log::debug!("data[{}] = {:x}", current_word, data[current_word as usize]);
                //wait_millisec(500);
                current_word += 1;
                i += 1;
                if i < words_to_read {
                    value >>= 16;
                    data[current_word as usize] = (value & 0xffff) as u16;
                    current_word += 1;
                }
                i += 1;
            }
            words -= words_to_read;
        }

        Ok(())
    })
}

fn checksum_ptr_x550<T: IxgbeOperations + ?Sized>(
    ops: &T,
    info: &PCIeInfo,
    mut ptr: u16,
    size: u16,
    csum: &mut u16,
    eeprom: &IxgbeEepromInfo,
) -> Result<(), IxgbeDriverErr> {
    let mut buf = [0; 256];
    let mut bufsz = 256;
    // Read a chunk at the pointer location
    if let Err(e) = read_ee_hostif_buffer_x550(ops, info, ptr, bufsz, &mut buf) {
        log::debug!("Failed to read EEPROM image\n");
        return Err(e);
    }

    let start;
    let mut length;
    if size != 0 {
        start = 0;
        length = size;
    } else {
        start = 1;
        length = buf[0];

        // Skip pointer section if length is invalid.
        if length == 0xFFFF || length == 0 || (ptr + length) >= eeprom.word_size {
            return Ok(());
        }
    }

    let mut i = start;
    while length > 0 {
        if i == bufsz {
            ptr += bufsz;
            i = 0;
            if length < bufsz {
                bufsz = length;
            }

            // Read a chunk at the pointer location
            if let Err(e) = read_ee_hostif_buffer_x550(ops, info, ptr, bufsz, &mut buf) {
                log::debug!("Failed to read EEPROM image\n");
                return Err(e);
            }
        }
        *csum += buf[i as usize];
        i += 1;
        length -= 1;
    }

    Ok(())
}

impl IxgbeOperations for IxgbeX550 {
    // MAC Operations

    // mac_reset_hw: IxgbeX540 - Perform hardware reset
    fn mac_reset_hw(&self, info: &mut PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        ixgbe_x540::mac_reset_hw_x540(self, info, hw)
    }

    fn mac_start_hw(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        ixgbe_x540::mac_start_hw_x540(self, info, hw)
    }

    fn mac_get_media_type(&self, _info: &PCIeInfo, _hw: &mut IxgbeHw) -> MediaType {
        MediaType::IxgbeMediaTypeCopper
    }

    fn mac_acquire_swfw_sync(&self, info: &PCIeInfo, mask: u32) -> Result<(), IxgbeDriverErr> {
        ixgbe_x540::mac_acquire_swfw_sync_x540(info, mask)
    }

    fn mac_release_swfw_sync(&self, info: &PCIeInfo, mask: u32) -> Result<(), IxgbeDriverErr> {
        ixgbe_x540::mac_release_swfw_sync_x540(info, mask)
    }

    fn mac_get_link_capabilities(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
    ) -> Result<(u32, bool), IxgbeDriverErr> {
        get_copper_link_capabilities(self, info, hw)
    }

    // setup_mac_link_X540 - Sets the auto advertised capabilities
    fn mac_setup_link(
        &self,
        info: &PCIeInfo,
        hw: &mut IxgbeHw,
        speed: u32,
        autoneg_wait_to_complete: bool,
    ) -> Result<(), IxgbeDriverErr> {
        self.phy_setup_link_speed(info, hw, speed, autoneg_wait_to_complete)
    }

    // disable_rx_x550 - Disable RX unit
    // Enables the Rx DMA unit for x550
    fn mac_disable_rx(&self, info: &PCIeInfo, hw: &mut IxgbeHw) -> Result<(), IxgbeDriverErr> {
        log::debug!("ixgbe_enable_rx_dma_x550");

        let mut rxctrl = ixgbe_hw::read_reg(info, IXGBE_RXCTRL)?;
        if rxctrl & IXGBE_RXCTRL_RXEN != 0 {
            let mut pfdtxgswc = ixgbe_hw::read_reg(info, IXGBE_PFDTXGSWC)?;
            if pfdtxgswc & IXGBE_PFDTXGSWC_VT_LBEN != 0 {
                pfdtxgswc &= !IXGBE_PFDTXGSWC_VT_LBEN;
                ixgbe_hw::write_reg(info, IXGBE_PFDTXGSWC, pfdtxgswc)?;
                hw.mac.set_lben = true;
            } else {
                hw.mac.set_lben = false;
            }

            let fw_cmd = IxgbeHicDisableRxen {
                hdr: IxgbeHicHdr {
                    cmd: FW_DISABLE_RXEN_CMD,
                    buf_len: FW_DISABLE_RXEN_LEN,
                    cmd_or_resp: 0,
                    checksum: FW_DEFAULT_CHECKSUM,
                },
                port_number: hw.bus.lan_id,
                pad2: 0,
                pad3: 0,
            };

            let ptr = &fw_cmd as *const IxgbeHicDisableRxen as *const u32;
            let size_in_u32 =
                core::mem::size_of::<IxgbeHicDisableRxen>() / core::mem::size_of::<u32>();
            let slice = unsafe { core::slice::from_raw_parts(ptr, size_in_u32) };

            if let Err(_) = ixgbe_operations::host_interface_command(
                self,
                info,
                slice,
                core::mem::size_of::<IxgbeHicDisableRxen>() as u32,
                IXGBE_HI_COMMAND_TIMEOUT,
                true,
            ) {
                // If we fail - disable RX using register write
                rxctrl = ixgbe_hw::read_reg(info, IXGBE_RXCTRL)?;
                if rxctrl & IXGBE_RXCTRL_RXEN != 0 {
                    rxctrl &= !IXGBE_RXCTRL_RXEN;
                    ixgbe_hw::write_reg(info, IXGBE_RXCTRL, rxctrl)?;
                }
            }
        }

        Ok(())
    }

    // PHY Operations

    // Using copper phy
    fn phy_set_power(&self, info: &PCIeInfo, hw: &IxgbeHw, on: bool) -> Result<(), IxgbeDriverErr> {
        ixgbe_x540::phy_set_power_x540(self, info, hw, on)
    }

    // EEPROM Operations

    // init_eeprom_params - Initialize EEPROM params
    // Initializes the EEPROM parameters ixgbe_eeprom_info within the
    // ixgbe_hw struct in order to set up EEPROM access.
    // Requires checking of EepromType to make sure that it is uninitialized beforehand
    fn eeprom_init_params(
        &self,
        info: &PCIeInfo,
        eeprom: &mut IxgbeEepromInfo,
    ) -> Result<(), IxgbeDriverErr> {
        eeprom.eeprom_type = EepromType::IxgbeFlash;
        eeprom.semaphore_delay = 10;

        let eec = ixgbe_hw::read_reg(info, get_eec_offset(info.get_id())?)?;
        let eeprom_size = ((eec & IXGBE_EEC_SIZE) >> IXGBE_EEC_SIZE_SHIFT) as u16;
        eeprom.word_size = 1 << (eeprom_size + IXGBE_EEPROM_WORD_SIZE_SHIFT);

        Ok(())
    }

    fn eeprom_read(
        &self,
        info: &PCIeInfo,
        _eeprom: &mut IxgbeEepromInfo,
        offset: u16,
        data: &mut [u16],
    ) -> Result<(), IxgbeDriverErr> {
        let mask = IXGBE_GSSR_SW_MNG_SM | IXGBE_GSSR_EEP_SM;
        let buffer = IxgbeHicReadShadowRam {
            hdr: IxgbeHicHdr2 {
                req: IxgbeHicHdr2Req {
                    cmd: FW_READ_SHADOW_RAM_CMD,
                    buf_lenh: 0,
                    buf_lenl: FW_READ_SHADOW_RAM_LEN,
                    checksum: FW_DEFAULT_CHECKSUM,
                },
            },
            // convert offset from words to bytes
            address: u32::to_be((offset * 2) as u32),
            // one word
            length: u16::to_be(core::mem::size_of::<u16>() as u16),
            pad2: 0,
            data: 0,
            pad3: 0,
        };

        log::debug!("ixgbe: eeprom_read");

        ixgbe_operations::mac_swfw_sync_mut(self, info, mask, 0, || {
            let ptr = &buffer as *const IxgbeHicReadShadowRam as *const u32;
            let size_in_u32 =
                core::mem::size_of::<IxgbeHicReadShadowRam>() / core::mem::size_of::<u32>();
            let slice = unsafe { core::slice::from_raw_parts(ptr, size_in_u32) };

            ixgbe_operations::hic_unlocked(
                info,
                slice,
                core::mem::size_of::<IxgbeHicReadShadowRam>() as u32,
                IXGBE_HI_COMMAND_TIMEOUT,
            )?;

            data[0] = ixgbe_hw::read_reg_array(info, IXGBE_FLEX_MNG, FW_NVM_DATA_OFFSET)? as u16;

            Ok(())
        })
    }

    fn eeprom_validate_checksum(&self, info: &PCIeInfo) -> Result<IxgbeEepromInfo, IxgbeDriverErr> {
        log::debug!("ixgbe_validate_eeprom_checksum_X550");

        let mut eeprom = IxgbeEepromInfo {
            eeprom_type: EepromType::IxgbeEepromUninitialized,
            semaphore_delay: 0,
            word_size: 0,
            address_bits: 0,
            word_page_size: 0,
            ctrl_word_3: 0,
        };
        let mut data = [0; 1];

        // Read the first word from the EEPROM. If this times out or fails, do
        // not continue or we could be in for a very long wait while every
        // EEPROM read fails
        if let Err(e) = self.eeprom_read(info, &mut eeprom, 0, &mut data) {
            log::debug!("EEPROM read failed");
            return Err(e);
        }

        let checksum = self.eeprom_calc_checksum(info, &mut eeprom)?;

        let mut read_checksum = [0; 1];

        // ixgbe_read_ee_hostif_X550() actually is eeprom->ops.read in OpenBSD
        // https://github.com/openbsd/src/blob/b21c4c927df760810943d63b35c0488ce22f755a/sys/dev/pci/ixgbe_x550.c#L155
        self.eeprom_read(info, &mut eeprom, IXGBE_EEPROM_CHECKSUM, &mut read_checksum)?;

        // Verify read checksum from EEPROM is the same as
        // calculated checksum
        if read_checksum[0] != checksum {
            log::error!("Invalid EEPROM checksum");
            return Err(IxgbeDriverErr::EepromChecksum);
        }

        Ok(eeprom)
    }

    // eeprom_calc_checksum - Calculates and returns the checksum
    // Returns a negative error code on error, or the 16-bit checksum
    fn eeprom_calc_checksum(
        &self,
        info: &PCIeInfo,
        eeprom: &mut IxgbeEepromInfo,
    ) -> Result<u16, IxgbeDriverErr> {
        log::debug!("ixgbe_calc_eeprom_checksum_X550");

        if eeprom.eeprom_type == EepromType::IxgbeEepromUninitialized {
            self.eeprom_init_params(info, eeprom)?;
        }

        let mut local_buffer = [0; IXGBE_EEPROM_LAST_WORD as usize + 1];
        // Read pointer area
        if let Err(e) =
            read_ee_hostif_buffer_x550(self, info, 0, IXGBE_EEPROM_LAST_WORD + 1, &mut local_buffer)
        {
            log::debug!("Failed to read EEPROM image");
            return Err(e);
        }

        // For X550 hardware include 0x0-0x41 in the checksum, skip the
        // checksum word itself
        let mut checksum = 0;
        for i in 0..=IXGBE_EEPROM_LAST_WORD as usize {
            if i != IXGBE_EEPROM_CHECKSUM as usize {
                checksum += local_buffer[i];
            }
        }
        log::debug!("0x0-0x41 checksum:{:x}", checksum);

        // Include all data from pointers 0x3, 0x6-0xE.  This excludes the
        // FW, PHY module, and PCIe Expansion/Option ROM pointers.
        for i in IXGBE_PCIE_ANALOG_PTR_X550..IXGBE_FW_PTR {
            if i == IXGBE_PHY_PTR || i == IXGBE_OPTION_ROM_PTR {
                continue;
            }
            let pointer = local_buffer[i as usize];

            // Skip pointer section if the pointer is invalid.
            if pointer == 0xFFFF || pointer == 0 || pointer >= eeprom.word_size {
                continue;
            }

            let size = match i {
                IXGBE_PCIE_GENERAL_PTR => IXGBE_IXGBE_PCIE_GENERAL_SIZE,
                IXGBE_PCIE_CONFIG0_PTR | IXGBE_PCIE_CONFIG1_PTR => IXGBE_PCIE_CONFIG_SIZE,
                _ => 0,
            };

            checksum_ptr_x550(self, info, pointer, size, &mut checksum, eeprom)?;
            //log::debug!("checksum{}:{:x}", i, checksum);
        }

        checksum = IXGBE_EEPROM_SUM - checksum;

        Ok(checksum)
    }
}

// Identical to X540, as seen in the OpenBSD: https://github.com/openbsd/src/blob/b21c4c927df760810943d63b35c0488ce22f755a/sys/dev/pci/ixgbe_x550.c#L145
// Return `(mcft_size: u32, vft_size: u32, num_rar_entries: u32,
// rx_pb_size: u32, max_rx_queues: u32, max_tx_queues: u32,
// max_msix_vectors: u16, arc_subsystem_valid: bool)`.
pub fn set_mac_val(
    info: &PCIeInfo,
) -> Result<(u32, u32, u32, u32, u32, u32, u16, bool), IxgbeDriverErr> {
    let arc_subsystem_valid =
        match ixgbe_hw::read_reg(info, IXGBE_FWSM_X540 & IXGBE_FWSM_MODE_MASK as usize) {
            Ok(val) => {
                if val == 0 {
                    false
                } else {
                    true
                }
            }
            Err(e) => return Err(e),
        };

    Ok((
        IXGBE_X540_MC_TBL_SIZE,
        IXGBE_X540_VFT_TBL_SIZE,
        IXGBE_X540_RAR_ENTRIES,
        IXGBE_X540_RX_PB_SIZE,
        IXGBE_X540_MAX_RX_QUEUES,
        IXGBE_X540_MAX_TX_QUEUES,
        0,
        arc_subsystem_valid,
    ))
}
