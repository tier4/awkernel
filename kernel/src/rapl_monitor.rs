use awkernel_async_lib::task::get_tasks_running;
use awkernel_lib::{
    arch::x86_64::{rapl::RaplEnergy, X86},
    sync::mutex::{MCSNode, Mutex},
};

const SAMPLE_INTERVAL_MS: u64 = 1_000;

static PREV: Mutex<Option<RaplEnergy>> = Mutex::new(None);

pub fn tick() {
    let Some(energy) = X86::rapl_read_energy() else {
        log::warn!("[RAPL] rapl_read_energy() returned None — RAPL not supported on this platform");
        return;
    };

    let mut node = MCSNode::new();
    let mut prev = PREV.lock(&mut node);

    if let Some(prev_e) = prev.take() {
        let busy = get_tasks_running().iter().any(|r| r.task_id != 0);

        // power_mW = delta_raw * 1_000_000 / (2^ESU * SAMPLE_INTERVAL_MS)
        let divisor = (1u64 << prev_e.energy_unit).saturating_mul(SAMPLE_INTERVAL_MS);

        let delta = |a: Option<u32>, b: Option<u32>| -> Option<(u32, u64)> {
            let d = b?.wrapping_sub(a?);
            Some((d, d as u64 * 1_000_000 / divisor))
        };

        let pkg  = delta(prev_e.pkg,  energy.pkg);
        let pp0  = delta(prev_e.pp0,  energy.pp0);
        let dram = delta(prev_e.dram, energy.dram);
        let pp1  = delta(prev_e.pp1,  energy.pp1);

        log::info!(
            "[RAPL] busy={busy} energy_unit={eu} \
             pkg={pkg_mw}mW(raw_delta={pkg_d}) \
             pp0={pp0_mw}mW(raw_delta={pp0_d}) \
             dram={dram_mw}mW(raw_delta={dram_d})",
            busy = busy,
            eu = prev_e.energy_unit,
            pkg_mw  = pkg .map(|(_, mw)| mw).unwrap_or(0),
            pkg_d   = pkg .map(|(d, _)| d as i64).unwrap_or(-1),
            pp0_mw  = pp0 .map(|(_, mw)| mw).unwrap_or(0),
            pp0_d   = pp0 .map(|(d, _)| d as i64).unwrap_or(-1),
            dram_mw = dram.map(|(_, mw)| mw).unwrap_or(0),
            dram_d  = dram.map(|(d, _)| d as i64).unwrap_or(-1),
        );
    } else {
        // 初回スナップショット取得時に raw 値を記録
        log::info!(
            "[RAPL] first snapshot — energy_unit={} pkg={:?} pp0={:?} dram={:?} pp1={:?}",
            energy.energy_unit, energy.pkg, energy.pp0, energy.dram, energy.pp1
        );
    }

    *prev = Some(energy);
}
