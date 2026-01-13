//! Interrupt remapping of Vt-d.

use acpi::AcpiTables;
use alloc::format;
use alloc::string::String;

use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    arch::x86_64::acpi::dmar::{dhrd::DmarDrhd, Dmar, DmarEntry},
    dma_pool::DMAPool,
    paging::PAGESIZE,
    sync::{mcs::MCSNode, mutex::Mutex},
};

use array_macro::array;

use super::acpi::AcpiMapper;

const TABLE_SIZE: usize = 256 * 4096; // 1MiB
const TABLE_ENTRY_NUM: usize = TABLE_SIZE / 16;

/// Error type for Vt-d interrupt remapping initialization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VtdError {
    /// Failed to enable Interrupt Remapping Table Pointer.
    IrtpEnableFailed,
    /// Failed to disable Interrupt Remapping Table Pointer.
    IrtpDisableFailed,
    /// Failed to enable Interrupt Remapping.
    IreEnableFailed,
    /// Failed to disable Interrupt Remapping.
    IreDisableFailed,
    /// Failed to enable Queued Invalidation.
    QieEnableFailed,
    /// Failed to disable Queued Invalidation.
    QieDisableFailed,
    /// Failed to allocate DMA memory.
    DmaAllocationFailed,
    /// Timeout waiting for command completion.
    Timeout,
}

impl core::fmt::Display for VtdError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            VtdError::IrtpEnableFailed => write!(f, "Failed to enable IRTP"),
            VtdError::IrtpDisableFailed => write!(f, "Failed to disable IRTP"),
            VtdError::IreEnableFailed => write!(f, "Failed to enable IRE"),
            VtdError::IreDisableFailed => write!(f, "Failed to disable IRE"),
            VtdError::QieEnableFailed => write!(f, "Failed to enable QIE"),
            VtdError::QieDisableFailed => write!(f, "Failed to disable QIE"),
            VtdError::DmaAllocationFailed => write!(f, "DMA allocation failed"),
            VtdError::Timeout => write!(f, "Timeout waiting for command completion"),
        }
    }
}

#[allow(dead_code)]
mod registers {
    use bitflags::bitflags;

    use crate::{mmio_r, mmio_rw, mmio_w};

    // `IRTEntry::flags`
    pub const PRESENT: u16 = 1;
    pub const FPD: u16 = 1 << 1; // Fault Processing Disable, 0: enable, 1: disable
    pub const DM: u16 = 1 << 2; // Destination Mode, 0: Physical, 1: Logical
    pub const RH: u16 = 1 << 3; // Redirection Hint, 0: directed to the processor listed in the Destination ID field, 1: directed to 1 of N processors specified in the Destination ID field
    pub const TM: u16 = 1 << 4; // Trigger Mode, 0: Edge, 1: Level

    // DLM in `IRTEntry::flags`
    pub const DLM_FIXED: u16 = 0b000 << 5; // Fixed, the destination ID is a fixed value
    pub const DLM_LOWEST: u16 = 0b001 << 5; // Lowest Priority
    pub const DLM_SMI: u16 = 0b010 << 5; // System Management Interrupt (SMI)
    pub const DLM_NMI: u16 = 0b100 << 5; // Non-Maskable Interrupt (NMI)
    pub const DLM_INIT: u16 = 0b101 << 5; // INIT
    pub const DLM_EXT_INIT: u16 = 0b111 << 5;

    pub const IM: u16 = 1 << 15; // IRTE Mode, 0: interrupt requests processed through this IRTE are remapped, 1: interrupt requests processed through this IRTE are remapped

    /// Source Validation Type
    /// 0b00: No source validation
    /// 0b01: Source validation by SID and SQ
    /// 0b10: Verify the most significant 8-bits of the requester-id
    /// 0b11: Reserved
    pub const SVT_SHIFT: u32 = 2;

    bitflags! {
        #[derive(Debug, Clone, Copy)]
        pub struct GlobalCommandStatus: u32 {
            const TE = 1 << 31;   // Translation Enable
            const RTP = 1 << 30;  // Root Table Pointer
            const WBF = 1 << 27;  // Write Buffer Flush
            const QIE = 1 << 26;  // Queued Invalidation Enable
            const IRE = 1 << 25;  // Interrupt Remapping Enable
            const IRTP = 1 << 24; // Interrupt Remapping Table Pointer
            const CFI = 1 << 23;  // Compatibility Format Interrupt
        }
    }

    pub const ICS_IWC: u32 = 1; // Invalidation Wait Descriptor Complete

    mmio_r!(offset 0x10 => pub EXTENDED_CAPABILITY<u64>);
    mmio_w!(offset 0x18 => pub GLOBAL_COMMAND<GlobalCommandStatus>);
    mmio_r!(offset 0x1c => pub GLOBAL_STATUS<GlobalCommandStatus>);
    mmio_rw!(offset 0x80 => pub IQH<u64>); // Invalidation Queue Head
    mmio_rw!(offset 0x88 => pub IQT<u64>); // Invalidation Queue Tail
    mmio_rw!(offset 0x90 => pub IQA<u64>); // Invalidation Queue Address
    mmio_r!(offset 0x9c => pub ICS<u32>); // Invalidation Completion Status
    mmio_rw!(offset 0xb8 => pub IRTA<u64>);
}

#[repr(C, packed)]
struct IRTEntry {
    flags: u16,
    vector: u8,
    _reserved1: u8,
    dest: u32,
    sid: u16,
    svt_sq: u16,
    _reserved2: u32,
}

impl IRTEntry {
    fn enable(
        &mut self,
        dest_apic_id: u32,
        irq: u8,
        level_trigger: bool,
        lowest_priority: bool,
        is_x2apic: bool,
    ) {
        let mut flags = registers::PRESENT | registers::FPD;

        if level_trigger {
            flags |= registers::TM;
        }

        if lowest_priority {
            flags |= registers::DLM_LOWEST;
        } else {
            flags |= registers::DLM_FIXED;
        }
        self.flags = flags;

        self.vector = irq;

        if is_x2apic {
            self.dest = dest_apic_id;
        } else {
            self.dest = (dest_apic_id & 0xff) << 8;
        }

        // TODO: check the source PCIe device
        self.sid = 0;
        self.svt_sq = 0;

        self._reserved1 = 0;
        self._reserved2 = 0;
    }

    fn disable(&mut self) {
        self.flags = 0;
    }
}

static INTERRUPT_REMAPPING: [Mutex<Option<InterruptRemapping>>; 32] =
    array![_ => Mutex::new(None); 32];

#[derive(Debug)]
pub struct RemapInfo {
    entry_id: usize,
    segment_number: usize,
}

impl RemapInfo {
    pub fn get_entry_id(&self) -> usize {
        self.entry_id
    }
}

impl Drop for RemapInfo {
    fn drop(&mut self) {
        let mut node = MCSNode::new();
        let mut table = INTERRUPT_REMAPPING[self.segment_number].lock(&mut node);

        if let Some(table) = table.as_mut() {
            table.deallocate_entry(self.entry_id);
        }
    }
}

#[derive(Debug)]
struct InterruptRemapping {
    table_base: VirtAddr,
    segment_number: usize,
    is_x2apic: bool,
}

impl InterruptRemapping {
    fn disable_all(&mut self) {
        let entries = unsafe { &mut *self.table_base.as_mut_ptr::<[IRTEntry; TABLE_ENTRY_NUM]>() };

        for entry in entries.iter_mut() {
            entry.disable();
        }
    }

    /// Allocate an entry in the Interrupt Remapping Table.
    /// This enables the remapping of the interrupt specified by `irq`.
    fn allocate_entry(
        &mut self,
        dest_apic_id: u32,
        irq: u8,
        level_trigger: bool,
        lowest_priority: bool,
    ) -> Option<RemapInfo> {
        let entries = unsafe { &mut *self.table_base.as_mut_ptr::<[IRTEntry; TABLE_ENTRY_NUM]>() };

        let mut result = None;

        for (i, entry) in entries.iter_mut().enumerate() {
            if entry.flags & registers::PRESENT == 0 {
                result = Some(i);
                break;
            }
        }

        let entry_id = result?;

        entries[entry_id].enable(
            dest_apic_id,
            irq,
            level_trigger,
            lowest_priority,
            self.is_x2apic,
        );

        Some(RemapInfo {
            entry_id,
            segment_number: self.segment_number,
        })
    }

    /// Deallocate an entry in the Interrupt Remapping Table.
    /// It disables the remapping of the interrupt specified by `entry_id`.
    fn deallocate_entry(&mut self, entry_id: usize) {
        assert!(entry_id < TABLE_ENTRY_NUM);

        let entries = unsafe { &mut *self.table_base.as_mut_ptr::<[IRTEntry; TABLE_ENTRY_NUM]>() };
        entries[entry_id].flags = 0;
    }
}

/// Initialize Interrupt Remapping.
///
/// # Safety
///
/// This function must be called only once.
pub unsafe fn init_interrupt_remap(
    phy_offset: VirtAddr,
    acpi: &AcpiTables<AcpiMapper>,
    is_x2apic: bool,
) -> Result<(), VtdError> {
    let mut remap_table = [None; 32];

    if let Ok(dmar) = acpi.find_table::<Dmar>() {
        for entry in dmar.entries() {
            if let DmarEntry::Drhd(drhd) = entry {
                drhd.device_scopes()
                    .find(|(scope, _path)| scope.entry_type == 1);

                if let Some((phy_addr, _virt_addr)) = &remap_table[drhd.segment_number as usize] {
                    let segment_number = drhd.segment_number as usize;
                    // Enable Interrupt Remapping
                    enable_interrupt_remapping(
                        segment_number,
                        phy_offset,
                        drhd,
                        *phy_addr,
                        is_x2apic,
                    )?;
                } else {
                    let segment_number = drhd.segment_number as usize;

                    let pool =
                        DMAPool::<[u8; TABLE_SIZE]>::new(segment_number, TABLE_SIZE / PAGESIZE)
                            .ok_or(VtdError::DmaAllocationFailed)?;

                    let virt_addr = pool.get_virt_addr();
                    let phy_addr = pool.get_phy_addr();
                    pool.leak();

                    // Enable Interrupt Remapping
                    enable_interrupt_remapping(
                        segment_number,
                        phy_offset,
                        drhd,
                        phy_addr,
                        is_x2apic,
                    )?;

                    remap_table[segment_number] = Some((phy_addr, virt_addr));
                }
            }
        }
    }

    // Set INTERRUPT_REMAPPING
    for (i, entry) in remap_table.iter().enumerate() {
        if let Some((_phy_addr, virt_addr)) = entry {
            let mut table = InterruptRemapping {
                table_base: *virt_addr,
                segment_number: i,
                is_x2apic,
            };

            table.disable_all();

            let mut node = MCSNode::new();
            INTERRUPT_REMAPPING[i].lock(&mut node).replace(table);
        }
    }

    Ok(())
}

/// Update GLOBAL_COMMAND register following Intel VT-d specification.
///
/// Steps:
/// 1. Read GLOBAL_STATUS register
/// 2. Reset one-shot bits (keeping only persistent bits)
/// 3. Set/clear the target bit
/// 4. Write to GLOBAL_COMMAND register
/// 5. Wait until GLOBAL_STATUS indicates command is serviced
fn update_global_command(
    vt_d_base: VirtAddr,
    bit_to_set: registers::GlobalCommandStatus,
    enable: bool,
) -> Result<(), VtdError> {
    // Step 1: Read GLOBAL_STATUS
    let status = registers::GLOBAL_STATUS.read(vt_d_base.as_usize());

    // Step 2: Reset one-shot bits
    // One-shot bits mask: 0x96FFFFFF (bits that should be preserved)
    let persistent_mask = registers::GlobalCommandStatus::from_bits_truncate(0x96FF_FFFF);
    let status_persistent = status & persistent_mask;

    // Step 3: Set or clear the target bit
    let command = if enable {
        status_persistent | bit_to_set
    } else {
        status_persistent & !bit_to_set
    };

    // Step 4: Write to GLOBAL_COMMAND
    registers::GLOBAL_COMMAND.write(command, vt_d_base.as_usize());

    // Step 5: Wait until GLOBAL_STATUS indicates command is serviced
    if wait_toggle_then_set(vt_d_base, bit_to_set, enable).is_err() {
        // Timeout: bit not updated as expected
        let current = registers::GLOBAL_STATUS.read(vt_d_base.as_usize());
        Err(
            if bit_to_set.contains(registers::GlobalCommandStatus::IRTP)
                && (enable && !current.contains(registers::GlobalCommandStatus::IRTP))
            {
                VtdError::IrtpEnableFailed
            } else if bit_to_set.contains(registers::GlobalCommandStatus::IRTP)
                && (!enable && current.contains(registers::GlobalCommandStatus::IRTP))
            {
                VtdError::IrtpDisableFailed
            } else if bit_to_set.contains(registers::GlobalCommandStatus::IRE)
                && (enable && !current.contains(registers::GlobalCommandStatus::IRE))
            {
                VtdError::IreEnableFailed
            } else if bit_to_set.contains(registers::GlobalCommandStatus::IRE)
                && (!enable && current.contains(registers::GlobalCommandStatus::IRE))
            {
                VtdError::IreDisableFailed
            } else if bit_to_set.contains(registers::GlobalCommandStatus::QIE)
                && (enable && !current.contains(registers::GlobalCommandStatus::QIE))
            {
                VtdError::QieEnableFailed
            } else if bit_to_set.contains(registers::GlobalCommandStatus::QIE)
                && (!enable && current.contains(registers::GlobalCommandStatus::QIE))
            {
                VtdError::QieDisableFailed
            } else {
                VtdError::Timeout // Default fallback
            },
        )
    } else {
        Ok(())
    }
}

fn wait_toggle_then_set(
    vt_d_base: VirtAddr,
    status_bit: registers::GlobalCommandStatus,
    enable: bool,
) -> Result<(), VtdError> {
    if enable {
        // wait until 1
        for _ in 0..1000 {
            if registers::GLOBAL_STATUS
                .read(vt_d_base.as_usize())
                .contains(status_bit)
            {
                return Ok(());
            }
        }
    } else {
        // wait until 0
        for _ in 0..1000 {
            if !registers::GLOBAL_STATUS
                .read(vt_d_base.as_usize())
                .contains(status_bit)
            {
                return Ok(());
            }
        }
    }

    Err(VtdError::Timeout)
}

/// Wait for register-based invalidation to complete.
/// This must be called before enabling Queued Invalidation.
fn wait_register_based_invalidation_complete(vt_d_base: VirtAddr) -> Result<(), VtdError> {
    // Wait for any pending register-based invalidation to complete
    // by checking the ICS register's IWC bit is 0
    for _ in 0..1000 {
        let ics = registers::ICS.read(vt_d_base.as_usize());
        if (ics & registers::ICS_IWC) == 0 {
            return Ok(());
        }
    }

    log::error!("Timeout waiting for register-based invalidation to complete");
    Err(VtdError::Timeout)
}

/// Set Interrupt Remapping Table Address Register.
///
/// 1. Set IRTA register
/// 2. Enable IRTP (Interrupt Remapping Table Pointer)
/// 3. Enable IRE (Interrupt Remapping Enable)
/// 4. Initialize Invalidation Queue
fn enable_interrupt_remapping(
    segment_number: usize,
    phy_offset: VirtAddr,
    drhd: &DmarDrhd,
    phy_addr: PhyAddr,
    is_x2apic: bool,
) -> Result<(), VtdError> {
    let vt_d_base = phy_offset + drhd.register_base_address as usize;

    // Extended Interrupt Mode (x2APIC) Enable
    let eime = if is_x2apic { 1 << 11 } else { 0 };
    let val = (phy_addr.as_usize() as u64 & !((1 << 12) - 1)) | eime | 0b1111; // Size

    registers::IRTA.write(val, vt_d_base.as_usize());

    // Enable IRTP (Interrupt Remapping Table Pointer)
    update_global_command(vt_d_base, registers::GlobalCommandStatus::IRTP, true)?;

    // Enable IRE (Interrupt Remapping Enable)
    update_global_command(vt_d_base, registers::GlobalCommandStatus::IRE, true)?;

    // Initialize Invalidation Queue
    init_invalidation_queue(segment_number, vt_d_base)?;

    // Re-read status after queue initialization
    let status = registers::GLOBAL_STATUS.read(vt_d_base.as_usize());

    let mut scope_str = String::new();

    for scope in drhd.device_scopes() {
        let (device_scope, path) = scope;
        scope_str = format!(
            "{scope_str}\r\nVt-d Device Scope: entry type = {}, length = {}, flags = 0x{:x}, enumeration ID = {}, start bus number = {}, path = {path:x?}",
            device_scope.entry_type,
            device_scope.length,
            device_scope.flags,
            device_scope.enumeration_id,
            device_scope.start_bus_number,
        );
    }

    log::info!(
            "Vt-d Interrupt Remapping: Segment = {segment_number}, Vt-d Base = 0x{:x}, Table PhyAddr = 0x{:x}, enabled = {}, mode = {}, extended capability = 0x{:x}, global status = 0x{:x}, IRTA = 0x{:x}, DHRD.flags = 0x{:x}{scope_str}",
            drhd.register_base_address as usize,
            phy_addr.as_usize(),
            status.contains(registers::GlobalCommandStatus::IRTP | registers::GlobalCommandStatus::IRE),
            if is_x2apic { "x2APIC" } else { "xAPIC" },
            registers::EXTENDED_CAPABILITY.read(vt_d_base.as_usize()),
            status.bits(),
            registers::IRTA.read(vt_d_base.as_usize()),
            drhd.flags
        );

    Ok(())
}

fn init_invalidation_queue(segment_number: usize, vt_d_base: VirtAddr) -> Result<(), VtdError> {
    // Wait for any pending register-based invalidation to complete
    // before enabling Queued Invalidation
    wait_register_based_invalidation_complete(vt_d_base)?;

    // Reset Invalidation Queue Tail
    registers::IQT.write(0, vt_d_base.as_usize());

    // Allocate a page for the Invalidation Queue
    let pool =
        DMAPool::<[u8; PAGESIZE]>::new(segment_number, 1).ok_or(VtdError::DmaAllocationFailed)?;

    let phy_addr = pool.get_phy_addr().as_usize() as u64;

    // bits[63:12] = Base (4KB aligned)
    // bit[11]     = DW (128/256)
    // bits[2:0]   = queue size (0 = 4KB)
    // bits[10:3]  = Reserved
    let iqa_value = phy_addr & !((1 << 12) - 1);
    registers::IQA.write(iqa_value, vt_d_base.as_usize());

    // Leak the pool to keep it allocated
    pool.leak();

    // Enable Queued Invalidation (QIE)
    update_global_command(vt_d_base, registers::GlobalCommandStatus::QIE, true)?;

    log::info!(
        "Vt-d Queued Invalidation enabled: Segment = {}, Queue PhyAddr = 0x{:x}, IQA = 0x{:x}, IQH = {}, IQT = {}",
        segment_number,
        phy_addr,
        registers::IQA.read(vt_d_base.as_usize()),
        registers::IQH.read(vt_d_base.as_usize()),
        registers::IQT.read(vt_d_base.as_usize())
    );

    Ok(())
}

pub fn allocate_remapping_entry(
    segment_number: usize,
    dest_apic_id: u32,
    irq: u8,
    level_trigger: bool,
    lowest_priority: bool,
) -> Option<RemapInfo> {
    let mut node = MCSNode::new();
    let mut table = INTERRUPT_REMAPPING[segment_number].lock(&mut node);

    if let Some(table) = table.as_mut() {
        table.allocate_entry(dest_apic_id, irq, level_trigger, lowest_priority)
    } else {
        None
    }
}
