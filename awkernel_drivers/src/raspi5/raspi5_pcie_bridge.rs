use core::ptr::{read_volatile, write_volatile};

/// Constants defining shifts and masks for PCI and PCIe configuration.
const PCI_SLOT_SHIFT: u32 = 3;
const PCI_SLOT_MASK: u32 = 0x1f;
const PCIE_SLOT_SHIFT: u32 = 15;
const PCIE_FUNC_SHIFT: u32 = 12;
const PCIE_BUSNUM_SHIFT: u32 = 20;
const PCI_FUNC_MASK: u32 = 0x07;

/// Base addresses for PCIe extended configuration space access.
const PCIE_EXT_CFG_INDEX: usize = 0x9000;
const PCIE_EXT_CFG_DATA: usize = 0x8000;

/// Addresses and masks for miscellaneous PCIe control registers.
const PCIE_MISC_UBUS_CTRL: usize = 0x40a4;
const PCIE_MISC_UBUS_CTRL_UBUS_PCIE_REPLY_ERR_DIS_MASK: u32 = 1 << 13;
const PCIE_MISC_UBUS_CTRL_UBUS_PCIE_REPLY_ERR_DIS_SHIFT: u32 = 13;
const PCIE_MISC_UBUS_CTRL_UBUS_PCIE_REPLY_DECERR_DIS_MASK: u32 = 1 << 19;
const PCIE_MISC_UBUS_CTRL_UBUS_PCIE_REPLY_DECERR_DIS_SHIFT: u32 = 19;
const PCIE_MISC_AXI_READ_ERROR_DATA: usize = 0x4170;
const PCIE_MISC_UBUS_TIMEOUT: usize = 0x40A8;
const PCIE_MISC_RC_CONFIG_RETRY_TIMEOUT: usize = 0x405c;
// const BRCM_MSI_TARGET_ADDR_LT_4GB: u64 = 0x0fffffffc;
// const BRCM_MSI_TARGET_ADDR_GT_4GB: u64 = 0xffffffffc;

const MEM_PCIE_RANGE_START: u64 = 0x1F00000000;
const MEM_PCIE_RANGE_SIZE: u64 = 0xFFFFFFFC;
const MEM_PCIE_RANGE_PCIE_START: u64 = 0x0000000000;

const PCIE_MISC_HARD_PCIE_HARD_DEBUG: usize = 0x4304;
const PCIE_MISC_HARD_PCIE_HARD_DEBUG_SERDES_IDDQ_MASK: u32 = 0x08000000;
const PCIE_MISC_HARD_PCIE_HARD_DEBUG_SERDES_IDDQ_SHIFT: u32 = 0x1b;
const PCIE_MISC_HARD_PCIE_HARD_DEBUG_CLKREQ_L1SS_ENABLE_MASK: u32 = 0x00200000;
const PCIE_MISC_HARD_PCIE_HARD_DEBUG_CLKREQ_DEBUG_ENABLE_MASK: u32 = 0x00000002;

// const PCIE_MISC_REVISION: usize = 0x406c;
const PCIE_MISC_MISC_CTRL: usize = 0x4008;
// const PCIE_MISC_RC_BAR2_CONFIG_LO_SIZE_MASK: u32 = 0x1f;
// const PCIE_MISC_RC_BAR2_CONFIG_LO_SIZE_SHIFT: u32 = 0;
const PCIE_MISC_RC_BAR2_CONFIG_LO: usize = 0x4034;
const PCIE_MISC_RC_BAR2_CONFIG_HI: usize = 0x4038;
const PCIE_MISC_UBUS_BAR2_CONFIG_REMAP: usize = 0x40b4;
const PCIE_MISC_MISC_CTRL_SCB0_SIZE_MASK: u32 = 0xf8000000;
const PCIE_MISC_MISC_CTRL_SCB0_SIZE_SHIFT: u32 = 0x1b;
const PCIE_MISC_RC_BAR1_CONFIG_LO: usize = 0x402c;
const PCIE_MISC_RC_BAR3_CONFIG_LO: usize = 0x403c;
const PCIE_MISC_CPU_2_PCIE_MEM_WIN0_LO: usize = 0x400c;
const PCIE_MISC_CPU_2_PCIE_MEM_WIN0_HI: usize = 0x4010;
const PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_HI: usize = 0x4080;
const PCIE_MISC_CPU_2_PCIE_MEM_WIN0_LIMIT_HI: usize = 0x4084;
const PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT: usize = 0x4070;

const PCIE_RC_CFG_PRIV1_ID_VAL3: usize = 0x043c;
const PCIE_RC_CFG_VENDOR_VENDOR_SPECIFIC_REG1: usize = 0x0188;
// const PCIE_RC_CFG_VENDOR_VENDOR_SPECIFIC_REG1_ENDIAN_MODE_BAR2_MASK: u32 = 0xC;
// const PCIE_RC_CFG_VENDOR_VENDOR_SPECIFIC_REG1_ENDIAN_MODE_BAR2_SHIFT: u32 = 2;

// const PCIE_RC_CFG_PRIV1_ID_VAL3_CLASS_CODE_MASK: u32 = 0xffffff;
// const PCIE_RC_CFG_PRIV1_ID_VAL3_CLASS_CODE_SHIFT: u32 = 0;

// const SIZE_MASK: u32 = 0x1f;
const SIZE_SHIFT: u32 = 0;

const PCI_HEADER_TYPE_NORMAL: u8 = 0;
const PCI_HEADER_TYPE_BRIDGE: u8 = 1;
const PCI_CLASS_REVISION: usize = 0x08;
const PCI_HEADER_TYPE: usize = 0x0e;
const PCI_CACHE_LINE_SIZE: usize = 0x0c;
// const PCI_PRIMARY_BUS: u64 = 0x18;
const PCI_SECONDARY_BUS: usize = 0x19;
const PCI_SUBORDINATE_BUS: usize = 0x1a;
const PCI_MEMORY_BASE: usize = 0x20;
const PCI_MEMORY_LIMIT: usize = 0x22;
const PCI_BRIDGE_CONTROL: usize = 0x3e;
const PCI_BRIDGE_CTL_PARITY: u8 = 0x01;
const BRCM_PCIE_CAP_REGS: usize = 0x00ac;
const PCI_EXP_RTCTL: usize = 28;
const PCI_EXP_RTCTL_CRSSVE: u16 = 0x0010;
const PCI_COMMAND: usize = 0x04;
const PCI_COMMAND_MEMORY: u16 = 0x2;
const PCI_COMMAND_MASTER: u16 = 0x4;
const PCI_COMMAND_SERR: u16 = 0x100;
const PCI_COMMAND_PARITY: u16 = 0x40;

// const PCI_STATUS: usize = 0x06;
// const PCI_STATUS_CAP_LIST: u16 = 0x10;
// const PCI_CAPABILITY_LIST: usize = 0x34;
// const PCI_CAP_ID_EXP: u16 = 0x10;
// const PCI_CAP_LIST_ID: usize = 0;
// const PCI_CAP_LIST_NEXT: usize = 1;
// const PCI_CAP_ID_MSI: u8 = 0x05;

// const RP1_PCIE_SLOT: u8 = 0;
// const RP1_PCIE_FUNC: u8 = 0;
// const RP1_PCI_CLASS_CODE: u32 = 0x20000;

const PCI_BASE_ADDRESS_0: usize = 0x10;

const PCI_BASE_ADDRESS_MEM_TYPE_64: u32 = 0x04;
const PCI_BASE_ADDRESS_1: usize = 0x14;
const PCI_INTERRUPT_PIN: usize = 0x3d;

const PCIE_RC_DL_MDIO_ADDR: usize = 0x1100;
const PCIE_RC_DL_MDIO_WR_DATA: usize = 0x1108;
const MDIO_DATA_DONE_MASK: u32 = 0x80000000;
const MDIO_PORT_SHIFT: u32 = 0x16;
const MDIO_REGAD_SHIFT: u32 = 0x0;
const MDIO_CMD_SHIFT: u32 = 0x14;
const MDIO_CMD_WRITE: u8 = 0x0;
const PCIE_RC_PL_PHY_CTL_15: usize = 0x184c;
const PCIE_RC_PL_PHY_CTL_15_PM_CLK_PERIOD_MASK: u32 = 0xff;
const MDIO_PORT0: u8 = 0x0;
const SET_ADDR_OFFSET: u8 = 0x1f;

const PCIE_GEN: u32 = 2;
const PCIE_LINK_STATE_L1: u32 = 1 << 1;
const PCIE_LINK_STATE_L0S: u32 = 1 << 0;
const PCIE_RC_CFG_PRIV1_LINK_CAPABILITY: usize = 0x04dc;
const PCIE_RC_CFG_PRIV1_LINK_CAPABILITY_ASPM_SUPPORT_MASK: u32 = 0xc00;
const PCIE_RC_CFG_PRIV1_LINK_CAPABILITY_ASPM_SUPPORT_SHIFT: u32 = 0xa;
const PCI_EXP_LNKCAP: usize = 12;
const PCI_EXP_LNKCTL2: usize = 48;
const PCI_EXP_LNKCAP_SLS: u32 = 0x0000000f;

const ARM_RESET_RESCAL_BASE: usize = 0x1000119500;
const BRCM_RESCAL_START: usize = 0x0;
const BRCM_RESCAL_START_BIT: u32 = 1 << 0;
// const BRCM_RESCAL_CTRL: usize = 0x4;
const BRCM_RESCAL_STATUS: usize = 0x8;
const BRCM_RESCAL_STATUS_BIT: u32 = 1 << 0;

// const PCIE_MISC_RC_BAR1_CONFIG_HI: usize = 0x4030;
// const PCIE_MISC_UBUS_BAR1_CONFIG_REMAP: usize = 0x40ac;
// const PCIE_MISC_UBUS_BAR1_CONFIG_REMAP_HI: usize = 0x40b0;
// const PCIE_MISC_UBUS_BAR1_CONFIG_REMAP_ACCESS_ENABLE_MASK: u32 = 1 << 0;

const ARM_RESET_BASE: usize = 0x1001504318;
const SW_INIT_SET: usize = 0x00;
const SW_INIT_CLEAR: usize = 0x04;
const SW_INIT_BANK_SIZE: usize = 0x18;

const PCIE_MISC_AXI_INTF_CTRL: u32 = 0x416c;
const AXI_REQFIFO_EN_QOS_PROPAGATION: u32 = 1 << 7;
const PCIE_MISC_CTRL_1: u32 = 0x40a0;
// const PCIE_MISC_CTRL_1_OUTBOUND_TC_MASK: u32 = 0xf;
// const PCIE_MISC_CTRL_1_OUTBOUND_NO_SNOOP_MASK: u32 = 1 << 3;
// const PCIE_MISC_CTRL_1_OUTBOUND_RO_MASK: u32 = 1 << 4;
const PCIE_MISC_CTRL_1_EN_VDM_QOS_CONTROL_MASK: u32 = 1 << 5;
const PCIE_MISC_VDM_PRIORITY_TO_QOS_MAP_LO: u32 = 0x4168;
const PCIE_MISC_VDM_PRIORITY_TO_QOS_MAP_HI: u32 = 0x4164;
const PCIE_RC_TL_VDM_CTL1: u32 = 0x0a0c;
// const PCIE_RC_TL_VDM_CTL1_VDM_VNDRID0_MASK: u32 = 0x0000ffff;
// const PCIE_RC_TL_VDM_CTL1_VDM_VNDRID1_MASK: u32 = 0xffff0000;
const PCIE_RC_TL_VDM_CTL0: u32 = 0x0a20;
const PCIE_RC_TL_VDM_CTL0_VDM_ENABLED_MASK: u32 = 0x10000;
const PCIE_RC_TL_VDM_CTL0_VDM_IGNORETAG_MASK: u32 = 0x20000;
const PCIE_RC_TL_VDM_CTL0_VDM_IGNOREVNDRID_MASK: u32 = 0x40000;

// const MMIO_ENDIAN: u32 = 0;
const PCIE_RC_CFG_VENDOR_SPCIFIC_REG1_LITTLE_ENDIAN: u32 = 0x0;
const PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT_NUM_MASK_BITS: u64 = 0xc;
const PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT_LIMIT_MASK: u32 = 0xfff00000;
const PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT_LIMIT_SHIFT: u32 = 0x14;
const PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT_BASE_MASK: u32 = 0xfff0;
const PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT_BASE_SHIFT: u32 = 0x4;
const PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_HI_BASE_MASK: u32 = 0xff;
const PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_HI_BASE_SHIFT: u32 = 0;

const PCIE_MISC_RC_BAR1_CONFIG_LO_SIZE_MASK: u32 = 0x1f;
const PCIE_MISC_RC_BAR3_CONFIG_LO_SIZE_MASK: u32 = 0x1f;

const PCIE_MISC_PCIE_STATUS: usize = 0x4068;
const PCIE_MISC_PCIE_STATUS_PCIE_DL_ACTIVE_MASK: u32 = 0x20;
const PCIE_MISC_PCIE_STATUS_PCIE_DL_ACTIVE_SHIFT: u32 = 0x5;
const PCIE_MISC_PCIE_STATUS_PCIE_PHYLINKUP_MASK: u32 = 0x10;
const PCIE_MISC_PCIE_STATUS_PCIE_PHYLINKUP_SHIFT: u32 = 0x4;

/// Extracts a specified field from a given value by applying a mask and a shift.
///
/// # Arguments
/// * `val` - The value from which to extract the field.
/// * `mask` - The bitmask to isolate the desired bits.
/// * `shift` - The number of bits to right-shift the masked value, aligning the field.
///
/// # Returns
/// The extracted field from the input value.
fn extract_field(val: u32, mask: u32, shift: u32) -> u32 {
    (val & mask) >> shift
}

/// Checks the status of the PCIe link to determine if it is active.
///
/// Reads PCIe status registers to verify that both the Data Link Layer and Physical Layer
/// are operational, indicating a healthy link between the host and device.
///
/// # Arguments
/// * `m_base` - The base memory address of the PCIe control registers.
///
/// # Returns
/// A boolean value indicating if the PCIe link is up (`true`) or down (`false`).
fn pcie_link_up(m_base: usize) -> bool {
    let val = read32(m_base + PCIE_MISC_PCIE_STATUS);
    let dla = extract_field(
        val,
        PCIE_MISC_PCIE_STATUS_PCIE_DL_ACTIVE_MASK,
        PCIE_MISC_PCIE_STATUS_PCIE_DL_ACTIVE_SHIFT,
    );
    let plu = extract_field(
        val,
        PCIE_MISC_PCIE_STATUS_PCIE_PHYLINKUP_MASK,
        PCIE_MISC_PCIE_STATUS_PCIE_PHYLINKUP_SHIFT,
    );

    dla != 0 && plu != 0
}

/// Configures PCIe clock request signaling for power management.
///
/// Disables debug features interfering with clock request signaling to enable
/// Active State Power Management (ASPM) for more efficient power utilization.
///
/// # Arguments
/// * `base_addr` - The base address of the PCIe miscellaneous control registers.
fn pcie_config_clkreq(base_addr: usize) {
    unsafe {
        let mut tmp =
            core::ptr::read_volatile((base_addr + PCIE_MISC_HARD_PCIE_HARD_DEBUG) as *const u32);
        tmp &= !PCIE_MISC_HARD_PCIE_HARD_DEBUG_CLKREQ_DEBUG_ENABLE_MASK;
        tmp &= !PCIE_MISC_HARD_PCIE_HARD_DEBUG_CLKREQ_L1SS_ENABLE_MASK;
        core::ptr::write_volatile(
            (base_addr + PCIE_MISC_HARD_PCIE_HARD_DEBUG) as *mut u32,
            tmp,
        );
    }
}

/// Sets the Quality of Service (QoS) for PCIe traffic classes.
///
/// Configures the AXI interface to prioritize traffic from different PCIe traffic classes,
/// improving data transfer efficiency and overall system performance.
///
/// # Arguments
/// * `base_addr` - The base address of the PCIe control registers.
fn pcie_set_tc_qos(base_addr: usize) {
    let mut reg = read32(base_addr + PCIE_MISC_AXI_INTF_CTRL as usize);
    reg &= !AXI_REQFIFO_EN_QOS_PROPAGATION;
    write32(base_addr + PCIE_MISC_AXI_INTF_CTRL as usize, reg);

    reg = read32(base_addr + PCIE_MISC_CTRL_1 as usize);
    reg &= !PCIE_MISC_CTRL_1_EN_VDM_QOS_CONTROL_MASK;
    write32(base_addr + PCIE_MISC_CTRL_1 as usize, reg);

    reg |= PCIE_MISC_CTRL_1_EN_VDM_QOS_CONTROL_MASK;
    write32(base_addr + PCIE_MISC_CTRL_1 as usize, reg);

    let qos_map: u32 = 0xBBAA9888;
    write32(
        base_addr + PCIE_MISC_VDM_PRIORITY_TO_QOS_MAP_LO as usize,
        qos_map,
    );
    write32(
        base_addr + PCIE_MISC_VDM_PRIORITY_TO_QOS_MAP_HI as usize,
        qos_map,
    );

    write32(base_addr + PCIE_RC_TL_VDM_CTL1 as usize, 0);

    reg = read32(base_addr + PCIE_RC_TL_VDM_CTL0 as usize);
    reg |= PCIE_RC_TL_VDM_CTL0_VDM_ENABLED_MASK
        | PCIE_RC_TL_VDM_CTL0_VDM_IGNORETAG_MASK
        | PCIE_RC_TL_VDM_CTL0_VDM_IGNOREVNDRID_MASK;
    write32(base_addr + PCIE_RC_TL_VDM_CTL0 as usize, reg);
}

fn sw_init_bit(id: u32) -> u32 {
    1 << (id & 0x1f)
}

fn sw_init_bank(id: u32) -> u32 {
    id >> 5
}

unsafe fn reset_assert(id: u32) {
    let off = sw_init_bank(id) as usize * SW_INIT_BANK_SIZE;
    write32(ARM_RESET_BASE + off + SW_INIT_SET, sw_init_bit(id));
}

unsafe fn reset_deassert(id: u32) {
    let off = sw_init_bank(id) as usize * SW_INIT_BANK_SIZE;
    write32(ARM_RESET_BASE + off + SW_INIT_CLEAR, sw_init_bit(id));

    delay_micros(480000);
}

unsafe fn pcie_bridge_sw_init_set(val: u32) {
    if val != 0 {
        reset_assert(44);
    } else {
        reset_deassert(44);
    }
}

fn read8(address: usize) -> u8 {
    unsafe { read_volatile(address as *const u8) }
}
fn read16(address: usize) -> u16 {
    unsafe { read_volatile(address as *const u16) }
}

fn read32(address: usize) -> u32 {
    unsafe { read_volatile(address as *const u32) }
}

fn write8(address: usize, value: u8) {
    unsafe {
        write_volatile(address as *mut u8, value);
    }
}
fn write16(address: usize, value: u16) {
    unsafe {
        write_volatile(address as *mut u16, value);
    }
}

fn write32(address: usize, value: u32) {
    unsafe {
        write_volatile(address as *mut u32, value);
    }
}

fn encode_ibar_size(size: u64) -> u32 {
    if size == 0 {
        return 0;
    }

    let log2_in = size.next_power_of_two().trailing_zeros();

    if (12..=15).contains(&log2_in) {
        (log2_in - 12) + 0x1c
    } else if (16..=37).contains(&log2_in) {
        log2_in - 15
    } else {
        0
    }
}

fn lower_32_bits(value: u64) -> u32 {
    (value & 0xFFFFFFFF) as u32
}

fn upper_32_bits(val: u64) -> u32 {
    (val >> 32) as u32
}

fn ilog2(v: u64) -> u32 {
    let mut l = 0;
    while (1 << l) < v {
        l += 1;
    }
    l
}

unsafe fn wr_fld(p: usize, mask: u32, shift: u32, val: u32) {
    let mut reg = read32(p);
    reg = (reg & !mask) | ((val << shift) & mask);
    write32(p, reg);
}

fn mdio_wt_done(x: u32) -> bool {
    (x & MDIO_DATA_DONE_MASK) != 0
}

fn pcie_mdio_form_pkt(port: u8, regad: u8, cmd: u8) -> u32 {
    ((port as u32) << MDIO_PORT_SHIFT)
        | ((regad as u32) << MDIO_REGAD_SHIFT)
        | ((cmd as u32) << MDIO_CMD_SHIFT)
}

fn pcie_munge_pll(m_base: usize) {
    let regs = [0x16, 0x17, 0x18, 0x19, 0x1b, 0x1c, 0x1e];
    let data = [0x50b9, 0xbda1, 0x0094, 0x97b4, 0x5030, 0x5030, 0x0007];

    let _ = pcie_mdio_write(m_base, MDIO_PORT0, SET_ADDR_OFFSET, 0x1600);

    for (&reg, &dat) in regs.iter().zip(data.iter()) {
        let _ = pcie_mdio_write(m_base, MDIO_PORT0, reg, dat);
    }
    delay_micros(10000);
}

fn set_gen(base: usize, gen: u32) {
    let lnkcap_addr = base + BRCM_PCIE_CAP_REGS + PCI_EXP_LNKCAP;
    let lnkctl2_addr = base + BRCM_PCIE_CAP_REGS + PCI_EXP_LNKCTL2;

    let mut lnkcap = read32(lnkcap_addr);
    lnkcap = (lnkcap & !PCI_EXP_LNKCAP_SLS) | gen;
    write32(lnkcap_addr, lnkcap);

    let mut lnkctl2 = read16(lnkctl2_addr);
    lnkctl2 = (lnkctl2 & !0xf) | gen as u16;
    write16(lnkctl2_addr, lnkctl2);
}

fn pcie_mdio_write(m_base: usize, port: u8, regad: u8, wrdata: u16) -> Result<(), ()> {
    let pkt = pcie_mdio_form_pkt(port, regad, MDIO_CMD_WRITE);
    write32(m_base + PCIE_RC_DL_MDIO_ADDR, pkt);
    read32(m_base + PCIE_RC_DL_MDIO_ADDR);
    write32(
        m_base + PCIE_RC_DL_MDIO_WR_DATA,
        MDIO_DATA_DONE_MASK | wrdata as u32,
    );

    let mut data = read32(m_base + PCIE_RC_DL_MDIO_WR_DATA);
    let mut tries = 0;
    while tries < 10 && !mdio_wt_done(data) {
        delay_micros(10000);
        data = read32(m_base + PCIE_RC_DL_MDIO_WR_DATA);
        tries += 1;
    }

    if mdio_wt_done(data) {
        Ok(())
    } else {
        Err(())
    }
}

/// Represents a memory window configuration for PCIe transactions.
struct MemWindow {
    cpu_addr: u64,
    pcie_addr: u64,
    size: u64,
}

/// Specifies a DMA range for data transfer between the CPU and PCIe devices.
struct DmaRange {
    pcie_addr: u64,
    cpu_addr: u64,
    size: u64,
}

/// Deasserts the reset signal for a given component, allowing it to begin or resume operation.
fn rescal_reset_deassert() -> Result<(), &'static str> {
    let base_addr = ARM_RESET_RESCAL_BASE;

    let mut reg = read32(base_addr + BRCM_RESCAL_START);
    write32(base_addr + BRCM_RESCAL_START, reg | BRCM_RESCAL_START_BIT);

    reg = read32(base_addr + BRCM_RESCAL_START);
    if reg & BRCM_RESCAL_START_BIT == 0 {
        return Err("Failed to start SATA/PCIe rescal");
    }

    loop {
        if read32(base_addr + BRCM_RESCAL_STATUS) & BRCM_RESCAL_STATUS_BIT != 0 {
            break;
        }

        delay_micros(10000);
    }

    reg = read32(base_addr + BRCM_RESCAL_START);
    write32(base_addr + BRCM_RESCAL_START, reg & !BRCM_RESCAL_START_BIT);

    Ok(())
}

fn delay_micros(micros: u64) {
    awkernel_lib::delay::wait_microsec(micros);
}

/// Configures an outbound memory window for PCIe transactions.
unsafe fn pcie_set_outbound_win(
    m_base: usize,
    win: usize,
    cpu_addr: u64,
    pcie_addr: u64,
    size: u64,
) {
    let cpu_addr_mb = cpu_addr >> 20;
    let limit_addr_mb = (cpu_addr + size - 1) >> 20;

    write32(
        m_base + PCIE_MISC_CPU_2_PCIE_MEM_WIN0_LO + (win * 8),
        lower_32_bits(pcie_addr),
    );

    write32(
        m_base + PCIE_MISC_CPU_2_PCIE_MEM_WIN0_HI + (win * 8),
        upper_32_bits(pcie_addr),
    );

    wr_fld(
        m_base + PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT + (win * 4),
        PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT_BASE_MASK,
        PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT_BASE_SHIFT,
        cpu_addr_mb as u32,
    );

    wr_fld(
        m_base + PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT + (win * 4),
        PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT_LIMIT_MASK,
        PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT_LIMIT_SHIFT,
        limit_addr_mb as u32,
    );

    let tmp_base_high =
        (cpu_addr_mb >> PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT_NUM_MASK_BITS) as u32;
    wr_fld(
        m_base + PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_HI + (win * 8),
        PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_HI_BASE_MASK,
        PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_HI_BASE_SHIFT,
        tmp_base_high,
    );

    let tmp_limit_high =
        (limit_addr_mb >> PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT_NUM_MASK_BITS) as u32;
    wr_fld(
        m_base + PCIE_MISC_CPU_2_PCIE_MEM_WIN0_LIMIT_HI + (win * 8),
        PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_HI_BASE_MASK,
        PCIE_MISC_CPU_2_PCIE_MEM_WIN0_BASE_HI_BASE_SHIFT,
        tmp_limit_high,
    );
}

fn cfg_index(busnr: u32, devfn: u32, reg: u32) -> u32 {
    (pci_slot(devfn) << PCIE_SLOT_SHIFT)
        | (pci_func(devfn) << PCIE_FUNC_SHIFT)
        | (busnr << PCIE_BUSNUM_SHIFT)
        | (reg & !3)
}

fn pci_slot(devfn: u32) -> u32 {
    (devfn >> PCI_SLOT_SHIFT) & PCI_SLOT_MASK
}

fn pci_func(devfn: u32) -> u32 {
    devfn & PCI_FUNC_MASK
}

fn pci_bus(n: u32) -> u32 {
    n
}

fn pci_bus2(n: u8) -> u8 {
    n
}

fn pci_devfn(slot: u32, func: u32) -> u32 {
    ((slot & 0x1f) << 3) | (func & 0x07)
}

pub struct CBcmPCIeHostBridge {
    pub m_base: usize,
}

impl CBcmPCIeHostBridge {
    /// Initializes the PCIe.
    ///
    /// # Safety
    pub unsafe fn pcie_init(&self) -> u8 {
        let mut m_out_wins: [MemWindow; 1] = [MemWindow {
            cpu_addr: 0,
            pcie_addr: 0,
            size: 0,
        }];

        m_out_wins[0].cpu_addr = MEM_PCIE_RANGE_START;
        m_out_wins[0].pcie_addr = MEM_PCIE_RANGE_PCIE_START;
        m_out_wins[0].size = MEM_PCIE_RANGE_SIZE;

        let mut m_dma_ranges: [DmaRange; 1] = [DmaRange {
            pcie_addr: 0,
            cpu_addr: 0,
            size: 0,
        }];
        m_dma_ranges[0].pcie_addr = 0x1000000000;
        m_dma_ranges[0].cpu_addr = 0;
        m_dma_ranges[0].size = 0;

        let rescal = rescal_reset_deassert();

        match rescal {
            Ok(_) => {}
            Err(_e) => {}
        }

        delay_micros(10000);
        pcie_bridge_sw_init_set(1);

        delay_micros(10000);
        pcie_bridge_sw_init_set(0);

        let m_base: usize = 0x1000120000;
        // let tmp: u32;
        // let mut m_rev: u32;
        wr_fld(
            m_base + PCIE_MISC_HARD_PCIE_HARD_DEBUG,
            PCIE_MISC_HARD_PCIE_HARD_DEBUG_SERDES_IDDQ_MASK,
            PCIE_MISC_HARD_PCIE_HARD_DEBUG_SERDES_IDDQ_SHIFT,
            0,
        );

        delay_micros(10000);

        // let mut address: usize = m_base + PCIE_MISC_REVISION;

        // tmp = read32(address);

        delay_micros(10000);

        // m_rev = tmp & 0xFFFF;

        pcie_munge_pll(m_base);

        let mut tmp = read32(m_base + PCIE_RC_PL_PHY_CTL_15);
        tmp &= !PCIE_RC_PL_PHY_CTL_15_PM_CLK_PERIOD_MASK;
        tmp |= 0x12;
        write32(m_base + PCIE_RC_PL_PHY_CTL_15, tmp);

        let address = m_base + PCIE_MISC_MISC_CTRL;

        tmp = read32(address);

        tmp = (tmp & !0x1000) | 0x1000;

        tmp = (tmp & !0x2000) | 0x2000;

        tmp = (tmp & !0x300000) | (0x300000 & (1 << 0x14));

        tmp = (tmp & !0x400) | 0x400;

        let target_address = m_base + PCIE_MISC_MISC_CTRL;

        write32(target_address, tmp);

        pcie_set_tc_qos(m_base);

        tmp = lower_32_bits(0x1000000000);

        let rc_bar2_size: u64 = 0;
        // let size_encoded = encode_ibar_size(rc_bar2_size);

        tmp = (tmp & !0x1f) | (0x1f & encode_ibar_size(rc_bar2_size));

        write32(m_base + PCIE_MISC_RC_BAR2_CONFIG_LO, tmp);

        let rc_bar2_offset: u64 = 0x1000000000;
        let value_to_write = (rc_bar2_offset >> 32) as u32;

        write32(m_base + PCIE_MISC_RC_BAR2_CONFIG_HI, value_to_write);

        tmp = read32(m_base + PCIE_MISC_UBUS_BAR2_CONFIG_REMAP);

        tmp = (tmp & !0x1) | 0x1;

        write32(m_base + PCIE_MISC_UBUS_BAR2_CONFIG_REMAP, tmp);

        let scb_size_val = if m_dma_ranges[0].size != 0 {
            ilog2(m_dma_ranges[0].size) - 15
        } else {
            0xf
        };

        wr_fld(
            m_base + PCIE_MISC_MISC_CTRL,
            PCIE_MISC_MISC_CTRL_SCB0_SIZE_MASK,
            PCIE_MISC_MISC_CTRL_SCB0_SIZE_SHIFT,
            scb_size_val,
        );

        tmp = read32(m_base + PCIE_MISC_UBUS_CTRL);
        tmp = (tmp & !PCIE_MISC_UBUS_CTRL_UBUS_PCIE_REPLY_ERR_DIS_MASK)
            | (1 << PCIE_MISC_UBUS_CTRL_UBUS_PCIE_REPLY_ERR_DIS_SHIFT);
        tmp = (tmp & !PCIE_MISC_UBUS_CTRL_UBUS_PCIE_REPLY_DECERR_DIS_MASK)
            | (1 << PCIE_MISC_UBUS_CTRL_UBUS_PCIE_REPLY_DECERR_DIS_SHIFT);

        write32(m_base + PCIE_MISC_UBUS_CTRL, tmp);
        write32(m_base + PCIE_MISC_AXI_READ_ERROR_DATA, 0xffffffff);
        write32(m_base + PCIE_MISC_UBUS_TIMEOUT, 0xB2D0000);
        write32(m_base + PCIE_MISC_RC_CONFIG_RETRY_TIMEOUT, 0xABA0000);

        // let m_msi_target_addr =
        //     if rc_bar2_offset >= 4 * GIGABYTE || (rc_bar2_size + rc_bar2_offset) < 4 * GIGABYTE {
        //         BRCM_MSI_TARGET_ADDR_LT_4GB
        //     } else {
        //         BRCM_MSI_TARGET_ADDR_GT_4GB
        //     };

        wr_fld(
            m_base + PCIE_MISC_RC_BAR1_CONFIG_LO,
            PCIE_MISC_RC_BAR1_CONFIG_LO_SIZE_MASK,
            SIZE_SHIFT,
            0,
        );
        wr_fld(
            m_base + PCIE_MISC_RC_BAR3_CONFIG_LO,
            PCIE_MISC_RC_BAR3_CONFIG_LO_SIZE_MASK,
            SIZE_SHIFT,
            0,
        );

        let aspm_support = PCIE_LINK_STATE_L1 | PCIE_LINK_STATE_L0S; //c 3

        let mut tmp = read32(m_base + PCIE_RC_CFG_PRIV1_LINK_CAPABILITY);

        tmp = (tmp & !PCIE_RC_CFG_PRIV1_LINK_CAPABILITY_ASPM_SUPPORT_MASK)
            | (PCIE_RC_CFG_PRIV1_LINK_CAPABILITY_ASPM_SUPPORT_MASK
                & (aspm_support << PCIE_RC_CFG_PRIV1_LINK_CAPABILITY_ASPM_SUPPORT_SHIFT));

        write32(m_base + PCIE_RC_CFG_PRIV1_LINK_CAPABILITY, tmp);

        set_gen(m_base, PCIE_GEN);

        tmp = read32(m_base + PCIE_RC_CFG_PRIV1_ID_VAL3);

        tmp = (tmp & !0xffffff) | (0xffffff & 0x060400);

        write32(m_base + PCIE_RC_CFG_PRIV1_ID_VAL3, tmp);

        pcie_set_outbound_win(
            m_base,
            0,
            m_out_wins[0].cpu_addr,
            m_out_wins[0].pcie_addr,
            m_out_wins[0].size,
        );

        tmp = read32(m_base + PCIE_RC_CFG_VENDOR_VENDOR_SPECIFIC_REG1);

        tmp = (tmp & !0xc) | (0xc & (PCIE_RC_CFG_VENDOR_SPCIFIC_REG1_LITTLE_ENDIAN << 0x2));

        write32(m_base + PCIE_RC_CFG_VENDOR_VENDOR_SPECIFIC_REG1, tmp);

        delay_micros(100000);

        tmp = read32(m_base + 0x4064);
        tmp = (tmp & !0x4) | 0x4;
        write32(m_base + 0x4064, tmp);

        let limit = 10;
        let mut j = 0;

        while j < limit && !pcie_link_up(m_base) {
            delay_micros(100000);
            j += 1;
        }

        pcie_config_clkreq(m_base);
        1
    }

    /// Enables a PCIe bridge device, configuring it for standard operation.
    ///
    /// Configures the primary PCIe bridge of the system, setting up bus numbers,
    /// memory mappings, and enabling necessary PCIe capabilities. This is typically
    /// one of the first steps in initializing PCIe support in a system.
    ///
    /// # Returns
    /// A result indicating success (`Ok`) or an error (`Err`) with an error code.
    pub fn enable_bridge(&self) -> Result<(), i32> {
        let conf = unsafe { self.pcie_map_conf(pci_bus(0), pci_devfn(0, 0), 0) };
        if conf == 0 {
            return Err(-1);
        }

        if read32(conf + PCI_CLASS_REVISION) >> 8 != 0x060400
            || read8(conf + PCI_HEADER_TYPE) != PCI_HEADER_TYPE_BRIDGE
        {
            return Err(-1);
        }

        write8(conf + PCI_CACHE_LINE_SIZE, 64 / 4);

        write8(conf + PCI_SECONDARY_BUS, pci_bus2(1));
        write8(conf + PCI_SUBORDINATE_BUS, pci_bus2(1));

        write16(
            conf + PCI_MEMORY_BASE,
            (MEM_PCIE_RANGE_PCIE_START >> 16) as u16,
        );
        write16(
            conf + PCI_MEMORY_LIMIT,
            (MEM_PCIE_RANGE_PCIE_START >> 16) as u16,
        );

        write8(conf + PCI_BRIDGE_CONTROL, PCI_BRIDGE_CTL_PARITY);

        write8(
            conf + BRCM_PCIE_CAP_REGS + PCI_EXP_RTCTL,
            PCI_EXP_RTCTL_CRSSVE as u8,
        );

        write16(
            conf + PCI_COMMAND,
            PCI_COMMAND_MEMORY | PCI_COMMAND_MASTER | PCI_COMMAND_PARITY | PCI_COMMAND_SERR,
        );

        Ok(())
    }

    /// Maps a configuration space for a given PCIe device.
    unsafe fn pcie_map_conf(&self, busnr: u32, devfn: u32, wheree: u32) -> usize {
        if busnr == 0 {
            return if pci_slot(devfn) == 0 {
                self.m_base + wheree as usize
            } else {
                0
            };
        }

        let idx = cfg_index(busnr, devfn, 0);
        write32(self.m_base + PCIE_EXT_CFG_INDEX, idx);
        self.m_base + PCIE_EXT_CFG_DATA + wheree as usize
    }

    /// Initializes a PCIe device, configuring it for operation.
    ///
    /// Prepares a PCIe device located at a specific slot and function on the bus for use.
    /// This includes setting up its base address registers (BARs) for memory access,
    /// enabling bus mastering for DMA, and ensuring it's ready to handle interrupts.
    ///
    /// # Arguments
    /// * `n_class_code` - The class code of the device to be initialized. Used to verify the device type.
    /// * `n_slot` - The slot on the PCIe bus where the device is located.
    /// * `n_func` - The function number of the device to initialize.
    ///
    /// # Returns
    /// A result indicating success (`Ok`) or an error (`Err`) with an error code if the device
    /// does not match the expected class code or cannot be configured properly.
    pub fn enable_device(&self, n_class_code: u32, n_slot: u32, n_func: u32) -> Result<(), i32> {
        let conf = unsafe { self.pcie_map_conf(pci_bus(1), pci_devfn(n_slot, n_func), 0) };
        if conf == 0 {
            return Err(-1);
        }

        delay_micros(100000);

        if read32(conf + PCI_CLASS_REVISION) >> 8 != n_class_code
            || read8(conf + PCI_HEADER_TYPE) != PCI_HEADER_TYPE_NORMAL
        {
            return Err(-1);
        }

        write8(conf + PCI_CACHE_LINE_SIZE, 64 / 4);

        write32(
            conf + PCI_BASE_ADDRESS_0,
            lower_32_bits(MEM_PCIE_RANGE_PCIE_START) | PCI_BASE_ADDRESS_MEM_TYPE_64,
        );
        write32(
            conf + PCI_BASE_ADDRESS_1,
            upper_32_bits(MEM_PCIE_RANGE_PCIE_START),
        );

        let uch_int_pin = read8(conf + PCI_INTERRUPT_PIN);
        if uch_int_pin != 1 {
            write8(conf + PCI_INTERRUPT_PIN, 1);
        }

        write16(
            conf + PCI_COMMAND,
            PCI_COMMAND_MEMORY | PCI_COMMAND_MASTER | PCI_COMMAND_PARITY | PCI_COMMAND_SERR,
        );

        Ok(())
    }
}
