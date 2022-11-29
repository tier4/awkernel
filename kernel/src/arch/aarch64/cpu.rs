use core::arch::asm;

pub const ECTLR_SMP_BIT: u64 = 1 << 6;

// Data cache set/way op type defines
pub const DCISW: u64 = 0x0;
pub const DCCISW: u64 = 0x1;

// SCR definitions
pub const SCR_RES1_BITS: u64 = (1 << 4) | (1 << 5);
pub const SCR_TWEDEL_SHIFT: u64 = 30;
pub const SCR_TWEDEL_MASK: u64 = 0xf;
pub const SCR_TWEDEN_BIT: u64 = 1 << 29;
pub const SCR_ECVEN_BIT: u64 = 1 << 28;
pub const SCR_FGTEN_BIT: u64 = 1 << 27;
pub const SCR_ATA_BIT: u64 = 1 << 26;
pub const SCR_FIEN_BIT: u64 = 1 << 21;
pub const SCR_EEL2_BIT: u64 = 1 << 18;
pub const SCR_API_BIT: u64 = 1 << 17;
pub const SCR_APK_BIT: u64 = 1 << 16;
pub const SCR_TERR_BIT: u64 = 1 << 15;
pub const SCR_TWE_BIT: u64 = 1 << 13;
pub const SCR_TWI_BIT: u64 = 1 << 12;
pub const SCR_ST_BIT: u64 = 1 << 11;
pub const SCR_RW_BIT: u64 = 1 << 10;
pub const SCR_SIF_BIT: u64 = 1 << 9;
pub const SCR_HCE_BIT: u64 = 1 << 8;
pub const SCR_SMD_BIT: u64 = 1 << 7;
pub const SCR_EA_BIT: u64 = 1 << 3;
pub const SCR_FIQ_BIT: u64 = 1 << 2;
pub const SCR_IRQ_BIT: u64 = 1 << 1;
pub const SCR_NS_BIT: u64 = 1 << 0;
pub const SCR_VALID_BIT_MASK: u64 = 0x2f8f;
pub const SCR_RESET_VAL: u64 = SCR_RES1_BITS;

// HCR definitions
pub const HCR_API_BIT: u64 = 1 << 41;
pub const HCR_APK_BIT: u64 = 1 << 40;
pub const HCR_E2H_BIT: u64 = 1 << 34;
pub const HCR_TGE_BIT: u64 = 1 << 27;
pub const HCR_RW_SHIFT: u64 = 31;
pub const HCR_RW_BIT: u64 = 1 << HCR_RW_SHIFT;
pub const HCR_AMO_BIT: u64 = 1 << 5;
pub const HCR_IMO_BIT: u64 = 1 << 4;
pub const HCR_FMO_BIT: u64 = 1 << 3;

// CPTR_EL2 definitions
pub const CPTR_EL2_RES1: u64 = (1 << 13) | (1 << 12) | (0x3ff);
pub const CPTR_EL2_TCPAC_BIT: u64 = 1 << 31;
pub const CPTR_EL2_TAM_BIT: u64 = 1 << 30;
pub const CPTR_EL2_TTA_BIT: u64 = 1 << 20;
pub const CPTR_EL2_TFP_BIT: u64 = 1 << 10;
pub const CPTR_EL2_TZ_BIT: u64 = 1 << 8;
pub const CPTR_EL2_RESET_VAL: u64 = CPTR_EL2_RES1;

// CNTHCTL_EL2 definitions
pub const CNTHCTL_RESET_VAL: u64 = 0x0;
pub const EVNTEN_BIT: u64 = 1 << 2;
pub const EL1PCEN_BIT: u64 = 1 << 1;
pub const EL1PCTEN_BIT: u64 = 1 << 0;

// VTTBR_EL2 definitions
pub const VTTBR_RESET_VAL: u64 = 0x0;
pub const VTTBR_VMID_MASK: u64 = 0xff;
pub const VTTBR_VMID_SHIFT: u64 = 48;
pub const VTTBR_BADDR_MASK: u64 = 0xffffffffffff;
pub const VTTBR_BADDR_SHIFT: u64 = 0;

// MDCR_EL2 definitions
pub const MDCR_EL2_HLP: u64 = 1 << 26;
pub const MDCR_EL2_HCCD: u64 = 1 << 23;
pub const MDCR_EL2_TTRF: u64 = 1 << 19;
pub const MDCR_EL2_HPMD: u64 = 1 << 17;
pub const MDCR_EL2_TPMS: u64 = 1 << 14;
pub const MDCR_EL2_E2PB_EL1: u64 = 0x3;
pub const MDCR_EL2_TDRA_BIT: u64 = 1 << 11;
pub const MDCR_EL2_TDOSA_BIT: u64 = 1 << 10;
pub const MDCR_EL2_TDA_BIT: u64 = 1 << 9;
pub const MDCR_EL2_TDE_BIT: u64 = 1 << 8;
pub const MDCR_EL2_HPME_BIT: u64 = 1 << 7;
pub const MDCR_EL2_TPM_BIT: u64 = 1 << 6;
pub const MDCR_EL2_TPMCR_BIT: u64 = 1 << 5;
pub const MDCR_EL2_RESET_VAL: u64 = 0x0;

pub fn mdcr_el2_e2pb(x: u64) -> u64 {
    x << 12
}

// PMCR_EL0 definitions
pub const PMCR_EL0_RESET_VAL: u64 = 0x0;
pub const PMCR_EL0_N_SHIFT: u64 = 11;
pub const PMCR_EL0_N_MASK: u64 = 0x1f;
pub const PMCR_EL0_N_BITS: u64 = PMCR_EL0_N_MASK << PMCR_EL0_N_SHIFT;
pub const PMCR_EL0_LP_BIT: u64 = 1 << 7;
pub const PMCR_EL0_LC_BIT: u64 = 1 << 6;
pub const PMCR_EL0_DP_BIT: u64 = 1 << 5;
pub const PMCR_EL0_X_BIT: u64 = 1 << 4;
pub const PMCR_EL0_D_BIT: u64 = 1 << 3;
pub const PMCR_EL0_C_BIT: u64 = 1 << 2;
pub const PMCR_EL0_P_BIT: u64 = 1 << 1;
pub const PMCR_EL0_E_BIT: u64 = 1 << 0;

// HSTR_EL2 definitions
pub const HSTR_EL2_RESET_VAL: u64 = 0x0;
pub const HSTR_EL2_T_MASK: u64 = 0xff;

// CNTHP_CTL_EL2 definitions
pub const CNTHP_CTL_ENABLE_BIT: u64 = 1 << 0;
pub const CNTHP_CTL_RESET_VAL: u64 = 0x0;

// SCTLR definitions
pub const SCTLR_EL2_RES1: u64 = (1 << 29)
    | (1 << 28)
    | (1 << 23)
    | (1 << 22)
    | (1 << 18)
    | (1 << 16)
    | (1 << 11)
    | (1 << 5)
    | (1 << 4);
pub const SCTLR_EL1_RES1: u64 =
    (1 << 29) | (1 << 28) | (1 << 23) | (1 << 22) | (1 << 20) | (1 << 11);
pub const SCTLR_AARCH32_EL1_RES1: u64 = (1 << 23) | (1 << 22) | (1 << 11) | (1 << 4) | (1 << 3);
pub const SCTLR_EL3_RES1: u64 = (1 << 29)
    | (1 << 28)
    | (1 << 23)
    | (1 << 22)
    | (1 << 18)
    | (1 << 16)
    | (1 << 11)
    | (1 << 5)
    | (1 << 4);
pub const SCTLR_M_BIT: u64 = 1 << 0;
pub const SCTLR_A_BIT: u64 = 1 << 1;
pub const SCTLR_C_BIT: u64 = 1 << 2;
pub const SCTLR_SA_BIT: u64 = 1 << 3;
pub const SCTLR_SA0_BIT: u64 = 1 << 4;
pub const SCTLR_CP15BEN_BIT: u64 = 1 << 5;
pub const SCTLR_ITD_BIT: u64 = 1 << 7;
pub const SCTLR_SED_BIT: u64 = 1 << 8;
pub const SCTLR_UMA_BIT: u64 = 1 << 9;
pub const SCTLR_I_BIT: u64 = 1 << 12;
pub const SCTLR_ENDB_BIT: u64 = 1 << 13;
pub const SCTLR_DZE_BIT: u64 = 1 << 14;
pub const SCTLR_UCT_BIT: u64 = 1 << 15;
pub const SCTLR_NTWI_BIT: u64 = 1 << 16;
pub const SCTLR_NTWE_BIT: u64 = 1 << 18;
pub const SCTLR_WXN_BIT: u64 = 1 << 19;
pub const SCTLR_UWXN_BIT: u64 = 1 << 20;
pub const SCTLR_IESB_BIT: u64 = 1 << 21;
pub const SCTLR_E0E_BIT: u64 = 1 << 24;
pub const SCTLR_EE_BIT: u64 = 1 << 25;
pub const SCTLR_UCI_BIT: u64 = 1 << 26;
pub const SCTLR_ENDA_BIT: u64 = 1 << 27;
pub const SCTLR_ENIB_BIT: u64 = 1 << 30;
pub const SCTLR_ENIA_BIT: u64 = 1 << 31;
pub const SCTLR_BT0_BIT: u64 = 1 << 35;
pub const SCTLR_BT1_BIT: u64 = 1 << 36;
pub const SCTLR_BT_BIT: u64 = 1 << 36;
pub const SCTLR_DSSBS_BIT: u64 = 1 << 44;
pub const SCTLR_RESET_VAL: u64 = SCTLR_EL3_RES1;

pub const MODE_SP_SHIFT: u64 = 0x0;
pub const MODE_SP_MASK: u64 = 0x1;
pub const MODE_SP_EL0: u64 = 0x0;
pub const MODE_SP_ELX: u64 = 0x1;

pub const MODE_RW_SHIFT: u64 = 0x4;
pub const MODE_RW_MASK: u64 = 0x1;
pub const MODE_RW_64: u64 = 0x0;
pub const MODE_RW_32: u64 = 0x1;

pub const MODE_EL_SHIFT: u64 = 0x2;
pub const MODE_EL_MASK: u64 = 0x3;
pub const MODE_EL_WIDTH: u64 = 0x2;
pub const MODE_EL3: u64 = 0x3;
pub const MODE_EL2: u64 = 0x2;
pub const MODE_EL1: u64 = 0x1;
pub const MODE_EL0: u64 = 0x0;

pub const MODE32_SHIFT: u64 = 0;
pub const MODE32_MASK: u64 = 0xf;
pub const MODE32_USR: u64 = 0x0;
pub const MODE32_FIQ: u64 = 0x1;
pub const MODE32_IRQ: u64 = 0x2;
pub const MODE32_SVC: u64 = 0x3;
pub const MODE32_MON: u64 = 0x6;
pub const MODE32_ABT: u64 = 0x7;
pub const MODE32_HYP: u64 = 0xa;
pub const MODE32_UND: u64 = 0xb;
pub const MODE32_SYS: u64 = 0xf;

// CPSR/SPSR definitions
pub const DAIF_FIQ_BIT: u64 = 1 << 0;
pub const DAIF_IRQ_BIT: u64 = 1 << 1;
pub const DAIF_ABT_BIT: u64 = 1 << 2;
pub const DAIF_DBG_BIT: u64 = 1 << 3;
pub const SPSR_DAIF_SHIFT: u64 = 6;
pub const SPSR_DAIF_MASK: u64 = 0xf;

pub const SPSR_AIF_SHIFT: u64 = 6;
pub const SPSR_AIF_MASK: u64 = 0x7;

pub const SPSR_E_SHIFT: u64 = 9;
pub const SPSR_E_MASK: u64 = 0x1;
pub const SPSR_E_LITTLE: u64 = 0x0;
pub const SPSR_E_BIG: u64 = 0x1;

pub const SPSR_T_SHIFT: u64 = 5;
pub const SPSR_T_MASK: u64 = 0x1;
pub const SPSR_T_ARM: u64 = 0x0;
pub const SPSR_T_THUMB: u64 = 0x1;

pub const SPSR_M_SHIFT: u64 = 4;
pub const SPSR_M_MASK: u64 = 0x1;
pub const SPSR_M_AARCH64: u64 = 0x0;
pub const SPSR_M_AARCH32: u64 = 0x1;

pub const SPSR_SSBS_BIT_AARCH64: u64 = 1 << 12;
pub const SPSR_SSBS_BIT_AARCH32: u64 = 1 << 23;

pub const DISABLE_ALL_EXCEPTIONS: u64 = DAIF_FIQ_BIT | DAIF_IRQ_BIT | DAIF_ABT_BIT | DAIF_DBG_BIT;

pub const DISABLE_INTERRUPTS: u64 = DAIF_FIQ_BIT | DAIF_IRQ_BIT;

// ID_AA64PFR0_EL1 definitions
pub const ID_AA64PFR0_EL0_SHIFT: u64 = 0;
pub const ID_AA64PFR0_EL1_SHIFT: u64 = 4;
pub const ID_AA64PFR0_EL2_SHIFT: u64 = 8;
pub const ID_AA64PFR0_EL3_SHIFT: u64 = 12;
pub const ID_AA64PFR0_AMU_SHIFT: u64 = 44;
pub const ID_AA64PFR0_AMU_MASK: u64 = 0xf;
pub const ID_AA64PFR0_ELX_MASK: u64 = 0xf;
pub const ID_AA64PFR0_GIC_SHIFT: u64 = 24;
pub const ID_AA64PFR0_GIC_WIDTH: u64 = 4;
pub const ID_AA64PFR0_GIC_MASK: u64 = 0xf;
pub const ID_AA64PFR0_SVE_SHIFT: u64 = 32;
pub const ID_AA64PFR0_SVE_MASK: u64 = 0xf;
pub const ID_AA64PFR0_SEL2_SHIFT: u64 = 36;
pub const ID_AA64PFR0_SEL2_MASK: u64 = 0xf;
pub const ID_AA64PFR0_MPAM_SHIFT: u64 = 40;
pub const ID_AA64PFR0_MPAM_MASK: u64 = 0xf;
pub const ID_AA64PFR0_DIT_SHIFT: u64 = 48;
pub const ID_AA64PFR0_DIT_MASK: u64 = 0xf;
pub const ID_AA64PFR0_DIT_LENGTH: u64 = 4;
pub const ID_AA64PFR0_DIT_SUPPORTED: u64 = 1;
pub const ID_AA64PFR0_CSV2_SHIFT: u64 = 56;
pub const ID_AA64PFR0_CSV2_MASK: u64 = 0xf;
pub const ID_AA64PFR0_CSV2_LENGTH: u64 = 4;

// ID_AA64PFR1_EL1 definitions
pub const ID_AA64PFR1_EL1_SSBS_SHIFT: u64 = 4;
pub const ID_AA64PFR1_EL1_SSBS_MASK: u64 = 0xf;

pub const SSBS_UNAVAILABLE: u64 = 0; // No architectural SSBS support

pub const ID_AA64PFR1_EL1_BT_SHIFT: u64 = 0;
pub const ID_AA64PFR1_EL1_BT_MASK: u64 = 0xf;

pub const BTI_IMPLEMENTED: u64 = 1; // The BTI mechanism is implemented

pub const ID_AA64PFR1_EL1_MTE_SHIFT: u64 = 8;
pub const ID_AA64PFR1_EL1_MTE_MASK: u64 = 0xf;

pub const MTE_UNIMPLEMENTED: u64 = 0;
pub const MTE_IMPLEMENTED_EL0: u64 = 1; // MTE is only implemented at EL0
pub const MTE_IMPLEMENTED_ELX: u64 = 2; // MTE is implemented at all ELs

pub const ID_AA64PFR1_MPAM_FRAC_SHIFT: u64 = 16;
pub const ID_AA64PFR1_MPAM_FRAC_MASK: u64 = 0xf;

// ID_AA64MMFR0_EL1 definitions
pub const ID_AA64MMFR0_EL1_PARANGE_SHIFT: u64 = 0;
pub const ID_AA64MMFR0_EL1_PARANGE_MASK: u64 = 0xf;

pub const PARANGE_0000: u64 = 32;
pub const PARANGE_0001: u64 = 36;
pub const PARANGE_0010: u64 = 40;
pub const PARANGE_0011: u64 = 42;
pub const PARANGE_0100: u64 = 44;
pub const PARANGE_0101: u64 = 48;
pub const PARANGE_0110: u64 = 52;

pub const ID_AA64MMFR0_EL1_ECV_SHIFT: u64 = 60;
pub const ID_AA64MMFR0_EL1_ECV_MASK: u64 = 0xf;
pub const ID_AA64MMFR0_EL1_ECV_NOT_SUPPORTED: u64 = 0x0;
pub const ID_AA64MMFR0_EL1_ECV_SUPPORTED: u64 = 0x1;
pub const ID_AA64MMFR0_EL1_ECV_SELF_SYNCH: u64 = 0x2;

pub const ID_AA64MMFR0_EL1_FGT_SHIFT: u64 = 56;
pub const ID_AA64MMFR0_EL1_FGT_MASK: u64 = 0xf;
pub const ID_AA64MMFR0_EL1_FGT_SUPPORTED: u64 = 0x1;
pub const ID_AA64MMFR0_EL1_FGT_NOT_SUPPORTED: u64 = 0x0;

pub const ID_AA64MMFR0_EL1_TGRAN4_SHIFT: u64 = 28;
pub const ID_AA64MMFR0_EL1_TGRAN4_MASK: u64 = 0xf;
pub const ID_AA64MMFR0_EL1_TGRAN4_SUPPORTED: u64 = 0x0;
pub const ID_AA64MMFR0_EL1_TGRAN4_NOT_SUPPORTED: u64 = 0xf;

pub const ID_AA64MMFR0_EL1_TGRAN64_SHIFT: u64 = 24;
pub const ID_AA64MMFR0_EL1_TGRAN64_MASK: u64 = 0xf;
pub const ID_AA64MMFR0_EL1_TGRAN64_SUPPORTED: u64 = 0x0;
pub const ID_AA64MMFR0_EL1_TGRAN64_NOT_SUPPORTED: u64 = 0xf;

pub const ID_AA64MMFR0_EL1_TGRAN16_SHIFT: u64 = 20;
pub const ID_AA64MMFR0_EL1_TGRAN16_MASK: u64 = 0xf;
pub const ID_AA64MMFR0_EL1_TGRAN16_SUPPORTED: u64 = 0x1;
pub const ID_AA64MMFR0_EL1_TGRAN16_NOT_SUPPORTED: u64 = 0x0;

// ID_AA64MMFR1_EL1 definitions
pub const ID_AA64MMFR1_EL1_TWED_SHIFT: u64 = 32;
pub const ID_AA64MMFR1_EL1_TWED_MASK: u64 = 0xf;
pub const ID_AA64MMFR1_EL1_TWED_SUPPORTED: u64 = 0x1;
pub const ID_AA64MMFR1_EL1_TWED_NOT_SUPPORTED: u64 = 0x0;

pub const MPIDR_AFFINITY_MASK: u64 = 0xff00ffffff;

pub enum EL {
    EL0t = 0b0000,
    EL1t = 0b0100,
    EL1h = 0b0101,
    EL2t = 0b1000,
    EL2h = 0b1001,
    EL3t = 0b1100,
    EL3h = 0b1101,
}

/// enable FP/SIMD on EL3
pub fn init_cptr_el3() {
    let val: u64 = 1 << 8; // enable FP/SIMD
    unsafe { asm!("msr CPTR_EL3, {}", in(reg) val) }
}

/// enable FP/SIMD on EL1
pub fn init_cpacr_el1() {
    let val: u64 = 0b110011 << 16;
    unsafe { asm!("msr CPACR_EL1, {}", in(reg) val) }
}

macro_rules! sysreg {
    ($x:ident) => {
        pub mod $x {
            use core::arch::asm;
            pub fn get() -> u64 {
                let v: u64;
                unsafe { asm!(concat!("mrs {}, ", stringify!($x)), lateout(reg) v) };
                v
            }

            pub fn set(v: u64) {
                unsafe { asm!(concat!("msr ", stringify!($x), ", {}"), in(reg) v) };
            }
        }
    }
}

sysreg!(daif);

sysreg!(cntp_ctl_el0);
sysreg!(cntp_cval_el0);
sysreg!(cntv_ctl_el0);
sysreg!(cntv_cval_el0);
sysreg!(cntfrq_el0);
sysreg!(cntpct_el0);
sysreg!(tpidr_el0);
sysreg!(tpidrro_el0);
sysreg!(pmcr_el0);
sysreg!(sp_el0);
sysreg!(ctr_el0);

sysreg!(elr_el1);
sysreg!(spsr_el1);
sysreg!(cntkctl_el1);
sysreg!(sctlr_el1);
sysreg!(actlr_el1);
sysreg!(cpacr_el1);
sysreg!(csselr_el1);
sysreg!(sp_el1);
sysreg!(esr_el1);
sysreg!(ttbr0_el1);
sysreg!(ttbr1_el1);
sysreg!(mair_el1);
sysreg!(amair_el1);
sysreg!(tcr_el1);
sysreg!(tpidr_el1);
sysreg!(par_el1);
sysreg!(far_el1);
sysreg!(afsr0_el1);
sysreg!(afsr1_el1);
sysreg!(contextidr_el1);
sysreg!(vbar_el1);
sysreg!(mpidr_el1);
sysreg!(midr_el1);
sysreg!(id_aa64pfr1_el1);
sysreg!(id_aa64mmfr0_el1);
sysreg!(id_aa64mmfr1_el1);
sysreg!(clidr_el1);

sysreg!(sctlr_el2);
sysreg!(mdcr_el2);
sysreg!(vpidr_el2);
sysreg!(vmpidr_el2);
sysreg!(vttbr_el2);
sysreg!(hcr_el2);
sysreg!(cptr_el2);
sysreg!(cnthctl_el2);
sysreg!(cntvoff_el2);
sysreg!(hstr_el2);
sysreg!(cnthp_ctl_el2);
sysreg!(esr_el2);
sysreg!(mair_el2);
sysreg!(tcr_el2);
sysreg!(ttbr0_el2);

sysreg!(scr_el3);
sysreg!(esr_el3);
sysreg!(far_el3);
sysreg!(sctlr_el3);
sysreg!(actlr_el3);
sysreg!(mair_el3);
sysreg!(cptr_el3);
sysreg!(ttbr0_el3);
sysreg!(tcr_el3);

pub fn get_affinity_lv0() -> u64 {
    let mpidr: u64;
    unsafe { asm!("mrs {}, mpidr_el1", lateout(reg) mpidr) };
    mpidr & 0xFF
}

pub fn get_affinity_lv1() -> u64 {
    let mpidr: u64;
    unsafe { asm!("mrs {}, mpidr_el1", lateout(reg) mpidr) };
    (mpidr >> 8) & 0xFF
}

pub fn get_current_el() -> u32 {
    let el: u64;
    unsafe { asm!("mrs {}, CurrentEL", lateout(reg) el) };
    ((el >> 2) & 0x3) as u32
}

pub fn get_sp() -> u64 {
    let sp: u64;
    unsafe { asm!("mov {}, sp", lateout(reg) sp) };
    sp
}

pub fn set_sp(sp: u64) {
    unsafe { asm!("mov sp, {}", in(reg) sp) };
}

pub fn get_armv8_5_mte_support() -> u64 {
    (id_aa64pfr1_el1::get() >> ID_AA64PFR1_EL1_MTE_SHIFT) & ID_AA64PFR1_EL1_MTE_MASK
}

pub fn is_armv8_6_twed_present() -> bool {
    ((id_aa64mmfr1_el1::get() >> ID_AA64MMFR1_EL1_TWED_SHIFT) & ID_AA64MMFR1_EL1_TWED_MASK)
        == ID_AA64MMFR1_EL1_TWED_SUPPORTED
}

pub fn is_armv8_6_fgt_present() -> bool {
    ((id_aa64mmfr0_el1::get() >> ID_AA64MMFR0_EL1_FGT_SHIFT) & ID_AA64MMFR0_EL1_FGT_MASK)
        == ID_AA64MMFR0_EL1_FGT_SUPPORTED
}

pub fn get_armv8_6_ecv_support() -> u64 {
    (id_aa64mmfr0_el1::get() >> ID_AA64MMFR0_EL1_ECV_SHIFT) & ID_AA64MMFR0_EL1_ECV_MASK
}

/// sev
pub fn send_event() {
    unsafe { asm!("sev") };
}

/// sevl
pub fn send_event_local() {
    unsafe { asm!("sevl") };
}

/// wfe
pub fn wait_event() {
    unsafe { asm!("wfe") };
}

/// wfi
pub fn wait_interrupt() {
    unsafe { asm!("wfi") };
}

/// dmb st
pub fn dmb_st() {
    unsafe { asm!("dmb st") };
}

/// dmb ld
pub fn dmb_ld() {
    unsafe { asm!("dmb ld") };
}

/// dmb sy
pub fn dmb_sy() {
    unsafe { asm!("dmb sy") };
}

/// dsb st
pub fn dsb_st() {
    unsafe { asm!("dsb st") };
}

/// dsb ld
pub fn dsb_ld() {
    unsafe { asm!("dsb ld") };
}

/// dsb sy
pub fn dsb_sy() {
    unsafe { asm!("dsb sy") };
}

/// dsb ish
pub fn dsb_ish() {
    unsafe { asm!("dsb ish") };
}

pub fn eret() {
    unsafe { asm!("eret") };
}

pub fn isb() {
    unsafe { asm!("isb") };
}

pub fn start_non_primary() {
    if cfg!(feature = "raspi3") {
        unsafe {
            asm!(
                "mov {0}, #0xe0
                 ldr {1}, =_start
                 str {1}, [{0}]
                 str {1}, [{0},  8] // core #2
                 str {1}, [{0}, 16] // core #3",
            lateout(reg) _,
            lateout(reg) _
            );
        }
    }
}

pub fn is_secure() -> bool {
    let scr = scr_el3::get();
    scr & SCR_NS_BIT == 0
}
