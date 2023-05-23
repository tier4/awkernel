use crate::arch::aarch64::page_table::{flags::*, PageTable};

pub struct Memory;

const TTBR1_ADDR: usize = 0xffff_ff80_0000_0000;

impl crate::memory::Memory for Memory {
    unsafe fn map(vm_addr: usize, phy_addr: usize, flag: crate::memory::Flag) -> bool {
        let mut page_table = get_page_table(vm_addr);

        let mut f = FLAG_L3_AF | FLAG_L3_ISH | FLAG_L3_ATTR_MEM | 0b11;

        if !flag.execute {
            f |= FLAG_L3_XN | FLAG_L3_PXN;
        }

        if flag.write {
            f |= FLAG_L3_SH_RW_N;
        } else {
            f |= FLAG_L3_SH_R_N;
        }

        page_table.unsafe_map(vm_addr as u64, phy_addr as u64, f)
    }

    unsafe fn unmap(vm_addr: usize) {
        let mut page_table = get_page_table(vm_addr);
        page_table.unmap(vm_addr as u64);
    }

    fn vm_to_phy(vm_addr: usize) -> Option<usize> {
        let page_table = get_page_table(vm_addr);

        if let Some(phy) = page_table.translate(vm_addr as u64) {
            Some(phy as usize)
        } else {
            None
        }
    }
}

fn get_page_table(vm_addr: usize) -> PageTable {
    let ttbr = if vm_addr >= TTBR1_ADDR {
        awkernel_aarch64::ttbr1_el1::get()
    } else {
        awkernel_aarch64::ttbr0_el1::get()
    };

    unsafe { PageTable::with_root(ttbr as usize) }
}
