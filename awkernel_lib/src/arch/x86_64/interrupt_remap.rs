//! Interrupt remapping of Vt-d.

use core::fmt::Debug;

use acpi::AcpiTables;

use crate::{
    addr::virt_addr::VirtAddr,
    arch::x86_64::acpi::dmar::{Dmar, DmarEntry},
    dma_pool::DMAPool,
    paging::{self, Frame, FrameAllocator, PageTable, PAGESIZE},
};

use super::acpi::AcpiMapper;

const PRESENT: u32 = 1;
const FPD: u32 = 1 << 1; // Fault Processing Disable, 0: enable, 1: disable
const DM: u32 = 1 << 2; // Destination Mode, 0: Physical, 1: Logical
const RH: u32 = 1 << 3; // Redirection Hint, 0: directed to the processor listed in the Destination ID field, 1: directed to 1 of N processors specified in the Destination ID field
const TM: u32 = 1 << 4; // Trigger Mode, 0: Edge, 1: Level

const DLM_FIXED: u32 = 0b000 << 5; // Fixed, the destination ID is a fixed value
const DLM_LOWEST: u32 = 0b001 << 5; // Lowest Priority
const DLM_SMI: u32 = 0b010 << 5; // System Management Interrupt (SMI)
const DLM_NMI: u32 = 0b100 << 5; // Non-Maskable Interrupt (NMI)
const DLM_INIT: u32 = 0b101 << 5; // INIT
const DLM_EXT_INIT: u32 = 0b111 << 5;

const IM: u32 = 1 << 15; // IRTE Mode, 0: interrupt requests processed through this IRTE are remapped, 1: interrupt requests processed through this IRTE are remapped

const V_SHIFT: u32 = 16; // Vector shift

/// Source Validation Type
/// 0b00: No source validation
/// 0b01: Source validation by SID and SQ
/// 0b10: Verify the most significant 8-bits of the requester-id
/// 0b11: Reserved
const SVT_SHIFT: u32 = 2;

#[repr(C, packed)]
struct IRTEntry {
    flags: u32,
    dest: u32,
    sid: u16,
    svt_sq: u16,
    reserved: u32,
}

impl IRTEntry {
    const fn new() -> Self {
        IRTEntry {
            flags: 0,
            dest: 0,
            sid: 0,
            svt_sq: 0,
            reserved: 0,
        }
    }

    fn enable(&mut self, irq: u8, level_trigger: bool, lowest_priority: bool) {
        let flags = PRESENT;
        // TODO
    }
}

/// # Safety
///
/// This function must be called only once.
pub unsafe fn init_interrupt_remap<F, FA, PT, E>(
    page_table_base: VirtAddr,
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut PT,
    page_allocators: &mut alloc::collections::BTreeMap<u32, FA>,
) -> Result<(), &'static str>
where
    F: Frame,
    FA: FrameAllocator<F, E>,
    PT: PageTable<F, FA, E>,
    E: Debug,
{
    const TABLE_SIZE: usize = 256 * 4096; // 1MiB

    let mut remap_table = [None; 32];

    if let Ok(dmar) = acpi.find_table::<Dmar>() {
        dmar.entries().for_each(|entry| {
            log::info!("{:x?}", entry);

            if let DmarEntry::Drhd(drhd) = entry {
                drhd.device_scopes()
                    .find(|(scope, _path)| scope.entry_type == 1);

                if let Some(_addr) = &remap_table[drhd.segment_number as usize] {
                    // TODO: Set Interrupt Remapping Table Address Register
                } else {
                    let pool = DMAPool::<[u8; TABLE_SIZE]>::new(
                        drhd.segment_number as usize,
                        TABLE_SIZE / PAGESIZE,
                    )
                    .expect("DMAPool::new() failed.");

                    let phy_addr = pool.get_phy_addr();
                    pool.leak();

                    remap_table[drhd.segment_number as usize] = Some(phy_addr);

                    // TODO: Set Interrupt Remapping Table Address Register
                }
            }
        });
    }

    let page_allocator = page_allocators.get_mut(&0).unwrap();
    let flags = paging::Flags {
        execute: false,
        write: true,
        cache: false,
        device: true,
        write_through: false,
    };

    for (i, table) in remap_table.into_iter().enumerate() {
        let Some(phy_addr) = table else {
            continue;
        };

        let virt_addr = VirtAddr::new(i * TABLE_SIZE) + page_table_base;

        unsafe {
            page_table
                .map_to(virt_addr, phy_addr, flags, page_allocator)
                .unwrap()
        };
    }

    Ok(())
}
