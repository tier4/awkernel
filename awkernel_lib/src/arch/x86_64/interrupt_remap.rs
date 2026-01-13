//! Interrupt remapping of Vt-d.

use core::sync::atomic::AtomicUsize;

use acpi::AcpiTables;
use alloc::{collections::linked_list::LinkedList, format, string::String};

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

static VTD_UNIT_IDX: AtomicUsize = AtomicUsize::new(0);

static DMA_POOL: [Mutex<Option<DMAPool<[u32; PAGESIZE / 4]>>>; 32] =
    array![_ => Mutex::new(None); 32];

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
    /// Invalidation Queue is full.
    QueueFull,
    /// Invalidation operation failed.
    InvalidationFailed,
    /// Fault status detected (IQE/ITE/ICE).
    FaultStatus(u32),
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
            VtdError::QueueFull => write!(f, "Invalidation Queue is full"),
            VtdError::InvalidationFailed => write!(f, "Invalidation operation failed"),
            VtdError::FaultStatus(status) => write!(f, "Fault status detected: 0x{:x}", status),
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

    pub const ICS_IWC: u32 = 1 << 0; // Invalidation Wait Descriptor Complete

    bitflags! {
        #[derive(Debug, Clone, Copy)]
        pub struct FaultStatus: u32 {
            const IQE = 1 << 4;  // Invalidation Queue Error
            const ICE = 1 << 5;  // Invalidation Completion Error
            const ITE = 1 << 6;  // Invalidation Time-out Error
        }
    }

    // Extended Capability Register bits
    pub const ECAP_ESIRTPS: u64 = 1 << 62; // Enhanced Set Interrupt Root Table Pointer Support

    mmio_r!(offset 0x10 => pub EXTENDED_CAPABILITY<u64>);
    mmio_w!(offset 0x18 => pub GLOBAL_COMMAND<GlobalCommandStatus>);
    mmio_r!(offset 0x1c => pub GLOBAL_STATUS<GlobalCommandStatus>);
    mmio_rw!(offset 0x34 => pub FSTS<u32>); // Fault Status Register
    mmio_rw!(offset 0x80 => pub IQH<u64>); // Invalidation Queue Head
    mmio_rw!(offset 0x88 => pub IQT<u64>); // Invalidation Queue Tail
    mmio_rw!(offset 0x90 => pub IQA<u64>); // Invalidation Queue Address
    mmio_rw!(offset 0x9c => pub ICS<u32>); // Invalidation Completion Status (W1C for IWC)
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

static IOMMU: [IommuInfo; 32] = array![x =>
    IommuInfo {
        segment_number: x,
        vtd_units: Mutex::new(LinkedList::new()),
        interrupt_remapping: Mutex::new(None),
    }; 32];

struct IommuInfo {
    segment_number: usize,
    vtd_units: Mutex<LinkedList<VtdUnit>>,
    interrupt_remapping: Mutex<Option<InterruptRemapping>>,
}

struct VtdUnit {
    vt_d_base: VirtAddr,
    iq_base: VirtAddr, // Cache Invalidation Queue base address
    index: usize,
}

#[derive(Debug)]
pub struct RemapInfo {
    entry_id: usize,
    segment_number: usize,
}

impl IommuInfo {
    fn dump(&self) -> Option<String> {
        let mut result = String::new();

        {
            let mut node = MCSNode::new();
            let vtd_units = self.vtd_units.lock(&mut node);

            if vtd_units.is_empty() {
                return None;
            }

            result = format!("VT-d Segment {}:", self.segment_number);

            for (i, vtd_unit) in vtd_units.iter().enumerate() {
                result = format!(
                    "{result}\r\n  VT-d Unit [{i}]: VT-d Base = 0x{:x}, IQ Base = 0x{:x}, Index = {}",
                    vtd_unit.vt_d_base.as_usize(),
                    vtd_unit.iq_base.as_usize(),
                    vtd_unit.index
                );
            }
        }

        {
            let mut node = MCSNode::new();
            let interrupt_remapping = self.interrupt_remapping.lock(&mut node);
            if let Some(table) = interrupt_remapping.as_ref() {
                result = format!(
                    "{result}\r\n  Interrupt Remapping Table: Base = 0x{:x}, is_x2apic = {}",
                    table.table_base.as_usize(),
                    table.is_x2apic
                );
            } else {
                result = format!("{result}\r\n  Interrupt Remapping Table: Not initialized");
            }
        }

        Some(result)
    }
}

impl RemapInfo {
    pub fn get_entry_id(&self) -> usize {
        self.entry_id
    }
}

impl Drop for RemapInfo {
    fn drop(&mut self) {
        log::debug!(
            "Vt-d: Deallocating interrupt remapping entry: segment = {}, entry_id = {}",
            self.segment_number,
            self.entry_id
        );

        let mut node = MCSNode::new();
        let mut table = IOMMU[self.segment_number]
            .interrupt_remapping
            .lock(&mut node);

        if let Some(table) = table.as_mut() {
            table.deallocate_entry(self.entry_id);

            core::sync::atomic::fence(core::sync::atomic::Ordering::Release);

            let mut node = MCSNode::new();
            let vtd_units = IOMMU[self.segment_number].vtd_units.lock(&mut node);
            for vtd_unit in vtd_units.iter() {
                if let Err(e) = invalidate_all_interrupt_entries(self.segment_number, vtd_unit) {
                    log::error!(
                        "Vt-d: Failed to invalidate interrupt entry after deallocation: segment = {}, entry_id = {}, error = {:?}",
                        self.segment_number,
                        self.entry_id,
                        e
                    );
                }
            }
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
                    let vt_d_base = phy_offset + drhd.register_base_address as usize;
                    enable_interrupt_remapping(
                        segment_number,
                        vt_d_base,
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
                    let vt_d_base = phy_offset + drhd.register_base_address as usize;
                    enable_interrupt_remapping(
                        segment_number,
                        vt_d_base,
                        drhd,
                        phy_addr,
                        is_x2apic,
                    )?;

                    remap_table[segment_number] = Some((phy_addr, virt_addr));
                }
            }
        }
    }

    // Set interrupt_remapping in IOMMU
    for (i, entry) in remap_table.iter().enumerate() {
        if let Some((_phy_addr, virt_addr)) = entry {
            let mut table = InterruptRemapping {
                table_base: *virt_addr,
                segment_number: i,
                is_x2apic,
            };

            table.disable_all();

            let mut node = MCSNode::new();
            IOMMU[i].interrupt_remapping.lock(&mut node).replace(table);
        }
    }

    // Perform global invalidation for all VT-d units
    // (unless ESIRTPS is supported, which handles this automatically)
    for (segment_number, iommu_info) in IOMMU.iter().enumerate() {
        let mut node = MCSNode::new();
        let vtd_units = iommu_info.vtd_units.lock(&mut node);

        for vtd_unit in vtd_units.iter() {
            let vt_d_base = vtd_unit.vt_d_base;
            let ecap = registers::EXTENDED_CAPABILITY.read(vt_d_base.as_usize());

            // Check if ESIRTPS is supported (bit 62)
            if (ecap & registers::ECAP_ESIRTPS) == 0 {
                // ESIRTPS not supported, need to perform global invalidation
                log::info!(
                    "VT-d segment {}: ESIRTPS not supported (ECAP=0x{:x}), performing global invalidation",
                    segment_number,
                    ecap
                );

                // Perform global invalidation using the vtd_unit reference
                invalidate_all_interrupt_entries(segment_number, vtd_unit)?;
            } else {
                log::debug!(
                    "VT-d segment {}: ESIRTPS supported (ECAP=0x{:x}), skipping global invalidation",
                    segment_number,
                    ecap
                );
            }
        }
    }

    dump_iommu_info();

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
        // For IRTP, wait until 0 first
        //
        // IRTPS:
        //   This field is cleared by hardware when software sets the SIRTP field in the
        //   Global Command register. This field is Set by hardware when hardware
        //   completes the ‘Set Interrupt Remap Table Pointer’ operation using the
        //   value provided in the Interrupt Remapping Table Address register.
        if status_bit.contains(registers::GlobalCommandStatus::IRTP) {
            for _ in 0..1000 {
                if !registers::GLOBAL_STATUS
                    .read(vt_d_base.as_usize())
                    .contains(registers::GlobalCommandStatus::IRTP)
                {
                    break;
                }
            }
        }

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

    log::error!("Vt-d: Timeout waiting for register-based invalidation to complete");
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
    vt_d_base: VirtAddr,
    drhd: &DmarDrhd,
    phy_addr: PhyAddr,
    is_x2apic: bool,
) -> Result<(), VtdError> {
    // Extended Interrupt Mode (x2APIC) Enable
    let eime = if is_x2apic { 1 << 11 } else { 0 };
    let val = (phy_addr.as_usize() as u64 & !((1 << 12) - 1)) | eime | 0b1111; // Size

    registers::IRTA.write(val, vt_d_base.as_usize());

    // Enable IRTP (Interrupt Remapping Table Pointer)
    update_global_command(vt_d_base, registers::GlobalCommandStatus::IRTP, true)?;

    // Initialize Invalidation Queue
    let iq_base = init_invalidation_queue(segment_number, vt_d_base)?;

    // Enable IRE (Interrupt Remapping Enable)
    update_global_command(vt_d_base, registers::GlobalCommandStatus::IRE, true)?;

    // Store VT-d unit info
    let index = VTD_UNIT_IDX.fetch_add(1, core::sync::atomic::Ordering::SeqCst);
    let vtd_unit = VtdUnit {
        vt_d_base,
        iq_base,
        index,
    };

    let mut node = MCSNode::new();
    IOMMU[segment_number]
        .vtd_units
        .lock(&mut node)
        .push_back(vtd_unit);

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

fn init_invalidation_queue(
    segment_number: usize,
    vt_d_base: VirtAddr,
) -> Result<VirtAddr, VtdError> {
    // Wait for any pending register-based invalidation to complete
    // before enabling Queued Invalidation
    wait_register_based_invalidation_complete(vt_d_base)?;

    // Reset Invalidation Queue Tail
    registers::IQT.write(0, vt_d_base.as_usize());

    // Allocate a page for the Invalidation Queue
    let pool =
        DMAPool::<[u8; PAGESIZE]>::new(segment_number, 1).ok_or(VtdError::DmaAllocationFailed)?;

    let phy_addr = pool.get_phy_addr().as_usize() as u64;
    let virt_addr = pool.get_virt_addr();

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

    Ok(virt_addr)
}

/// Invalidation Queue Descriptor Types
#[repr(C, align(16))]
#[derive(Debug, Clone, Copy)]
struct InvalidationDescriptor {
    lo: u64,
    hi: u64,
}

impl InvalidationDescriptor {
    /// Create Interrupt Entry Cache Invalidation Descriptor
    fn interrupt_entry_cache_invalidation(index: u16, index_mask: u16, granularity: u8) -> Self {
        let lo = 0x04 // Type: Interrupt Entry Cache Invalidation
            | ((granularity as u64) << 4) // Bits [4]: Granularity
            | ((index_mask as u64) << 27) // Bits [31:27]: Interrupt Index Mask (IM)
            | ((index as u64) << 32); // Bits [47:32]: Interrupt Index (IIDX)
        Self { lo, hi: 0 }
    }

    /// Create Invalidation Wait Descriptor
    fn invalidation_wait(status_write: bool, status_data: u32, status_addr: u64) -> Self {
        let lo = 0x05 // Type: Invalidation Wait Descriptor
            | if status_write { 1 << 5 } else { 0 } // SW: Status Write
            | (1 << 6) // FN: When Set, indicates descriptors following the invalidation wait descriptor must be processed by hardware only after the invalidation wait descriptor completes.
            | ((status_data as u64) << 32);
        let hi = status_addr;
        Self { lo, hi }
    }
}

const QUEUE_SIZE_BYTES: usize = PAGESIZE; // 4KB
const DESCRIPTOR_SIZE: usize = 16; // 128-bit descriptor
const QUEUE_ENTRIES: usize = QUEUE_SIZE_BYTES / DESCRIPTOR_SIZE; // 256 entries

/// Push a descriptor to the Invalidation Queue
fn push_invalidation_descriptor(
    segment_number: usize,
    vt_d_base: VirtAddr,
    iq_base: VirtAddr,
    descriptor: InvalidationDescriptor,
) -> Result<(), VtdError> {
    // Read current head and tail
    let head = registers::IQH.read(vt_d_base.as_usize()) as usize;
    let tail = registers::IQT.read(vt_d_base.as_usize()) as usize;

    // Convert to entry indices (tail/head are byte offsets, 16B aligned)
    let head_idx = head / DESCRIPTOR_SIZE;
    let tail_idx = tail / DESCRIPTOR_SIZE;

    // Check if queue is full (next tail would catch up to head)
    let next_tail_idx = (tail_idx + 1) % QUEUE_ENTRIES;
    if next_tail_idx == head_idx {
        log::error!(
            "Vt-d: Invalidation Queue full: segment = {}, head = {}, tail = {}",
            segment_number,
            head_idx,
            tail_idx
        );
        return Err(VtdError::QueueFull);
    }

    // Write descriptor to IQ[tail]
    let queue = unsafe { &mut *(iq_base.as_mut_ptr::<[InvalidationDescriptor; QUEUE_ENTRIES]>()) };
    queue[tail_idx] = descriptor;

    // Memory fence to ensure descriptor is visible before updating IQT
    // This is critical for DMA coherency
    core::sync::atomic::fence(core::sync::atomic::Ordering::Release);

    // Update IQT (doorbell) - this is a byte offset, must be 16B aligned
    let new_tail = (next_tail_idx * DESCRIPTOR_SIZE) as u64;
    registers::IQT.write(new_tail, vt_d_base.as_usize());

    log::trace!(
        "Vt-d: Pushed descriptor to IQ: segment = {}, tail_idx = {} -> {}, descriptor = {:?}",
        segment_number,
        tail_idx,
        next_tail_idx,
        descriptor
    );

    Ok(())
}

/// Wait for invalidation completion by checking ICS or using wait descriptor
fn wait_invalidation_complete(segment_number: usize, vtd_unit: &VtdUnit) -> Result<(), VtdError> {
    let vt_d_base = vtd_unit.vt_d_base;
    let iq_base = vtd_unit.iq_base;

    // Create and push Invalidation Wait descriptor
    let mut node = MCSNode::new();
    let mut dma_pool = DMA_POOL[segment_number].lock(&mut node);

    if dma_pool.is_none() {
        let pool = DMAPool::<[u32; PAGESIZE / 4]>::new(segment_number, 1)
            .ok_or(VtdError::DmaAllocationFailed)?;
        *dma_pool = Some(pool);
    }

    let status_addr; // Physical address of the status word
    let status; // Mutable reference to the status word

    if let Some(dma_pool) = dma_pool.as_mut() {
        status_addr = (dma_pool.get_phy_addr().as_usize() + vtd_unit.index * 4) as u64;
        status = dma_pool.as_mut();
    } else {
        return Err(VtdError::DmaAllocationFailed);
    }

    // Initialize status word to 0
    status[vtd_unit.index] = 0;
    core::sync::atomic::fence(core::sync::atomic::Ordering::Release);

    // Create Invalidation Wait descriptor
    // When the invalidation is complete, hardware writes 1 to status_addr.
    let wait_desc = InvalidationDescriptor::invalidation_wait(true, 1, status_addr);
    push_invalidation_descriptor(segment_number, vt_d_base, iq_base, wait_desc)?;

    for _ in 0..10000 {
        // Check for fault status before checking completion
        let fsts = registers::FSTS.read(vt_d_base.as_usize());
        let fault_flags = registers::FaultStatus::from_bits_truncate(fsts);
        if fault_flags.intersects(
            registers::FaultStatus::IQE | registers::FaultStatus::ITE | registers::FaultStatus::ICE,
        ) {
            log::error!(
                "Vt-d: Invalidation fault detected: segment = {}, FSTS = 0x{:x}, fault_flags = {:?}",
                segment_number,
                fsts,
                fault_flags
            );

            // Clear fault status bits (W1C)
            registers::FSTS.write(fsts, vt_d_base.as_usize());

            return Err(VtdError::FaultStatus(fsts));
        }

        // Check for completion
        core::sync::atomic::fence(core::sync::atomic::Ordering::Acquire);
        if status[0] != 0 {
            return Ok(());
        }
    }

    log::warn!(
        "Vt-d: Invalidation wait timeout: segment = {}, IQH = 0x{:x}, IQT = 0x{:x}",
        segment_number,
        registers::IQH.read(vt_d_base.as_usize()),
        registers::IQT.read(vt_d_base.as_usize())
    );

    Err(VtdError::Timeout)
}

/// Invalidate interrupt entry cache for a specific index
fn invalidate_interrupt_entry(
    segment_number: usize,
    vtd_unit: &VtdUnit,
    interrupt_index: u16,
) -> Result<(), VtdError> {
    let vt_d_base = vtd_unit.vt_d_base;
    let iq_base = vtd_unit.iq_base;

    // Create Interrupt Entry Cache Invalidation descriptor
    // Granularity = 1 (index-selective), index_mask = 0 (specific index)
    let desc = InvalidationDescriptor::interrupt_entry_cache_invalidation(interrupt_index, 0, 1);

    // Push descriptor to queue
    push_invalidation_descriptor(segment_number, vt_d_base, iq_base, desc)?;

    // Wait for completion
    wait_invalidation_complete(segment_number, vtd_unit)?;

    log::trace!(
        "Vt-d: Invalidated interrupt entry: segment = {}, index = {}, vtd_base = 0x{:x}, iq_base = 0x{:x}, IQH = 0x{:x}, IQT = 0x{:x}",
        segment_number,
        interrupt_index,
        vt_d_base.as_usize(),
        iq_base.as_usize(),
        registers::IQH.read(vt_d_base.as_usize()),
        registers::IQT.read(vt_d_base.as_usize())
    );

    Ok(())
}

/// Invalidate all interrupt entries (global invalidation)
fn invalidate_all_interrupt_entries(
    segment_number: usize,
    vtd_unit: &VtdUnit,
) -> Result<(), VtdError> {
    let vt_d_base = vtd_unit.vt_d_base;
    let iq_base = vtd_unit.iq_base;

    // Create global Interrupt Entry Cache Invalidation descriptor
    // Granularity = 0 (global)
    let desc = InvalidationDescriptor::interrupt_entry_cache_invalidation(0, 0, 0);

    // Push descriptor to queue
    push_invalidation_descriptor(segment_number, vt_d_base, iq_base, desc)?;

    // Wait for completion
    wait_invalidation_complete(segment_number, vtd_unit)?;

    log::info!(
        "Vt-d: Invalidated all interrupt entries: segment = {}, vtd_base = 0x{:x}, iq_base = 0x{:x}, IQH = 0x{:x}, IQT = 0x{:x}",
        segment_number,
        vt_d_base.as_usize(),
        iq_base.as_usize(),
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
    let mut table = IOMMU[segment_number].interrupt_remapping.lock(&mut node);

    if let Some(table) = table.as_mut() {
        let remap_info = table.allocate_entry(dest_apic_id, irq, level_trigger, lowest_priority)?;

        core::sync::atomic::fence(core::sync::atomic::Ordering::Release);

        let mut node = MCSNode::new();
        let vtd_units = IOMMU[segment_number].vtd_units.lock(&mut node);
        for vtd_unit in vtd_units.iter() {
            if let Err(e) =
                invalidate_interrupt_entry(segment_number, vtd_unit, remap_info.entry_id as u16)
            {
                log::error!(
                    "Vt-d: Failed to invalidate interrupt entry after allocation: segment = {}, entry_id = {}, error = {:?}",
                    segment_number,
                    remap_info.entry_id,
                    e
                );
            }
        }

        Some(remap_info)
    } else {
        None
    }
}

fn dump_iommu_info() {
    let mut result = String::new();

    for iommu_info in IOMMU.iter() {
        if let Some(dump) = iommu_info.dump() {
            result = format!("{result}\r\n{dump}");
        }
    }

    log::info!("Vt-d IOMMU Info: {result}");
}
