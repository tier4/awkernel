use awkernel_async_lib::task::get_tasks_running;
use awkernel_lib::{
    arch::x86_64::{rapl::RaplEnergy, X86},
    cpu::num_cpu,
    sync::mutex::{MCSNode, Mutex},
    time::Time,
};

const SAMPLE_INTERVAL_MS: u64 = 1_000;

static PREV: Mutex<Option<(RaplEnergy, u64)>> = Mutex::new(None);

pub fn tick() {
    let t_ms = Time::now().uptime().as_millis() as u64;

    let Some(energy) = X86::rapl_read_energy() else {
        log::warn!("[RAPL] not supported on this platform");
        return;
    };

    let mut node = MCSNode::new();
    let mut prev = PREV.lock(&mut node);

    if let Some((prev_e, prev_t)) = prev.take() {
        let dt_ms = t_ms.saturating_sub(prev_t).max(1);

        let running = get_tasks_running();
        let active = running.iter().filter(|r| r.task_id != 0).count();
        let total = num_cpu();

        // power_mW = delta_raw * 1_000_000 / (2^ESU * dt_ms)
        let divisor = (1u64 << prev_e.energy_unit).saturating_mul(dt_ms);

        let to_mw = |a: Option<u32>, b: Option<u32>| -> u64 {
            if let (Some(a), Some(b)) = (a, b) {
                b.wrapping_sub(a) as u64 * 1_000_000 / divisor
            } else {
                0
            }
        };

        log::info!(
            "[RAPL] t={}ms dt={}ms cpus={}/{} pkg={}mW pp0(cores)={}mW dram={}mW pp1(igpu)={}mW",
            t_ms,
            dt_ms,
            active,
            total,
            to_mw(prev_e.pkg,  energy.pkg),
            to_mw(prev_e.pp0,  energy.pp0),
            to_mw(prev_e.dram, energy.dram),
            to_mw(prev_e.pp1,  energy.pp1),
        );
    }

    *prev = Some((energy, t_ms));
}
