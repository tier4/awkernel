//! Interrupt remapping of Vt-d.

use acpi::AcpiTables;
use alloc::format;

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

    mmio_r!(offset 0x10 => pub EXTENDED_CAPABILITY<u64>);
    mmio_w!(offset 0x18 => pub GLOBAL_COMMAND<GlobalCommandStatus>);
    mmio_r!(offset 0x1c => pub GLOBAL_STATUS<GlobalCommandStatus>);
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
) -> Result<(), &'static str> {
    let mut remap_table = [None; 32];

    if let Ok(dmar) = acpi.find_table::<Dmar>() {
        dmar.entries().for_each(|entry| {
            if let DmarEntry::Drhd(drhd) = entry {
                drhd.device_scopes()
                    .find(|(scope, _path)| scope.entry_type == 1);

                if let Some((phy_addr, _virt_addr)) = &remap_table[drhd.segment_number as usize] {
                    let segment_number = drhd.segment_number as usize;
                    // Set Interrupt Remapping Table Address Register
                    set_irta(segment_number, phy_offset, drhd, *phy_addr, is_x2apic);
                } else {
                    let segment_number = drhd.segment_number as usize;

                    let pool =
                        DMAPool::<[u8; TABLE_SIZE]>::new(segment_number, TABLE_SIZE / PAGESIZE)
                            .expect("DMAPool::new() failed.");

                    let virt_addr = pool.get_virt_addr();
                    let phy_addr = pool.get_phy_addr();
                    pool.leak();

                    // Set Interrupt Remapping Table Address Register
                    set_irta(segment_number, phy_offset, drhd, phy_addr, is_x2apic);

                    remap_table[segment_number] = Some((phy_addr, virt_addr));
                }
            }
        });
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

/// Set Interrupt Remapping Table Address Register.
fn set_irta(
    segment_number: usize,
    phy_offset: VirtAddr,
    drhd: &DmarDrhd,
    phy_addr: PhyAddr,
    is_x2apic: bool,
) {
    let vt_d_base = phy_offset + drhd.register_base_address as usize;

    // Extended Interrupt Mode (x2APIC) Enable
    let eime = if is_x2apic { 1 << 11 } else { 0 };
    let val = (phy_addr.as_usize() as u64 & !((1 << 12) - 1)) | eime | 0b1111; // Size

    registers::IRTA.write(val, vt_d_base.as_usize());

    let stat = registers::GlobalCommandStatus::IRTP | registers::GlobalCommandStatus::IRE;
    registers::GLOBAL_COMMAND.write(stat, vt_d_base.as_usize());

    // Wait until enabled
    for _ in 0..100 {
        let stat = registers::GLOBAL_STATUS.read(vt_d_base.as_usize());
        if stat.contains(registers::GlobalCommandStatus::IRTP | registers::GlobalCommandStatus::IRE)
        {
            break;
        }
    }

    if !registers::GLOBAL_STATUS
        .read(vt_d_base.as_usize())
        .contains(registers::GlobalCommandStatus::IRTP | registers::GlobalCommandStatus::IRE)
    {
        log::error!("Failed to enable Vt-d Interrupt Remapping.");
        return;
    }

    let stat = registers::GLOBAL_STATUS.read(vt_d_base.as_usize());

    let mut scope_str = format!("");

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
            stat.contains(registers::GlobalCommandStatus::IRTP | registers::GlobalCommandStatus::IRE),
            if is_x2apic { "x2APIC" } else { "xAPIC" },
            registers::EXTENDED_CAPABILITY.read(vt_d_base.as_usize()),
            stat.bits(),
            registers::IRTA.read(vt_d_base.as_usize()),
            drhd.flags
        )
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
