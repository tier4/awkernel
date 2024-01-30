//! Interrupt remapping of Vt-d.

use core::ptr::{read_volatile, write_volatile};

use acpi::AcpiTables;

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

// `IRTEntry::flags`
const PRESENT: u16 = 1;
const FPD: u16 = 1 << 1; // Fault Processing Disable, 0: enable, 1: disable
const DM: u16 = 1 << 2; // Destination Mode, 0: Physical, 1: Logical
const RH: u16 = 1 << 3; // Redirection Hint, 0: directed to the processor listed in the Destination ID field, 1: directed to 1 of N processors specified in the Destination ID field
const TM: u16 = 1 << 4; // Trigger Mode, 0: Edge, 1: Level

// DLM in `IRTEntry::flags`
const DLM_FIXED: u16 = 0b000 << 5; // Fixed, the destination ID is a fixed value
const DLM_LOWEST: u16 = 0b001 << 5; // Lowest Priority
const DLM_SMI: u16 = 0b010 << 5; // System Management Interrupt (SMI)
const DLM_NMI: u16 = 0b100 << 5; // Non-Maskable Interrupt (NMI)
const DLM_INIT: u16 = 0b101 << 5; // INIT
const DLM_EXT_INIT: u16 = 0b111 << 5;

const IM: u16 = 1 << 15; // IRTE Mode, 0: interrupt requests processed through this IRTE are remapped, 1: interrupt requests processed through this IRTE are remapped

/// Source Validation Type
/// 0b00: No source validation
/// 0b01: Source validation by SID and SQ
/// 0b10: Verify the most significant 8-bits of the requester-id
/// 0b11: Reserved
const SVT_SHIFT: u32 = 2;

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
    const fn new() -> Self {
        IRTEntry {
            flags: 0,
            vector: 0,
            _reserved1: 0,
            dest: 0,
            sid: 0,
            svt_sq: 0,
            _reserved2: 0,
        }
    }

    fn enable(&mut self, irq: u8, level_trigger: bool, lowest_priority: bool) {
        let flags = PRESENT;
        // TODO
    }
}

static INTERRUPT_REMAPPING: [Mutex<Option<InterruptRemapping>>; 32] =
    array![_ => Mutex::new(None); 32];

#[derive(Debug)]
struct InterruptRemapping {
    table_base: VirtAddr,
    segment_number: usize,
}

impl InterruptRemapping {
    fn disable_all(&mut self) {
        let entries = unsafe { &mut *self.table_base.as_mut_ptr::<[IRTEntry; TABLE_ENTRY_NUM]>() };

        for entry in entries.iter_mut() {
            entry.flags = 0;
        }
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
) -> Result<(), &'static str> {
    let mut remap_table = [None; 32];

    if let Ok(dmar) = acpi.find_table::<Dmar>() {
        dmar.entries().for_each(|entry| {
            if let DmarEntry::Drhd(drhd) = entry {
                drhd.device_scopes()
                    .find(|(scope, _path)| scope.entry_type == 1);

                if let Some((phy_addr, _virt_addr)) = &remap_table[drhd.segment_number as usize] {
                    // Set Interrupt Remapping Table Address Register
                    set_irta(phy_offset, drhd, *phy_addr);
                } else {
                    let segment_number = drhd.segment_number as usize;

                    let pool =
                        DMAPool::<[u8; TABLE_SIZE]>::new(segment_number, TABLE_SIZE / PAGESIZE)
                            .expect("DMAPool::new() failed.");

                    let virt_addr = pool.get_virt_addr();
                    let phy_addr = pool.get_phy_addr();
                    pool.leak();

                    remap_table[segment_number] = Some((phy_addr, virt_addr));

                    // Set Interrupt Remapping Table Address Register
                    set_irta(phy_offset, drhd, phy_addr);

                    log::info!(
                        "Vt-d Interrupt Remapping Table: Segment = {}, PhyAddr = 0x{:x}, VirtAddr = 0x{:x}",
                        segment_number,
                        phy_addr.as_usize(),
                        virt_addr.as_usize()
                    )
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
            };

            table.disable_all();

            let mut node = MCSNode::new();
            INTERRUPT_REMAPPING[i].lock(&mut node).replace(table);
        }
    }

    Ok(())
}

/// Set Interrupt Remapping Table Address Register
fn set_irta(phy_offset: VirtAddr, drhd: &DmarDrhd, phy_addr: PhyAddr) {
    let irta_reg = phy_offset + drhd.register_base_address as usize + 0xb8;
    let ptr = irta_reg.as_mut_ptr::<u64>();
    unsafe {
        let val = read_volatile(ptr);
        let val = (phy_addr.as_usize() as u64 & !((1 << 12) - 1))
                        | (val & (1 << 11)) // Extended Interrupt Mode Enable
                        | 0b1111; // Size

        write_volatile(ptr, val);
    }
}
