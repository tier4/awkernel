//! Per-CPU task execution trace recorder.
//!
//! Unlike the `perf` module (which accumulates totals), this module records a
//! timeline of events: which task started/ended on which CPU at which time.
//! The dump can be turned into a per-core Gantt chart on the host.
//!
//! Design notes:
//! - Each CPU owns its buffer; the write index is claimed with a per-CPU
//!   `fetch_add`, so recording is lock-free and safe against preemption.
//! - Timestamps are raw CPU counter values (TSC on x86).  A pair of
//!   (cpu_counter, uptime µs) calibration points taken at `start()` and
//!   `stop()` lets the host convert ticks to wall-clock time.
//! - `events()` must only be called after `stop()`; a record racing past the
//!   enabled-check may at worst leave one torn event at the tail.

use alloc::vec::Vec;
use array_macro::array;
use awkernel_lib::cpu::NUM_MAX_CPU;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

/// Maximum number of events recorded per CPU.
/// 32768 events x 16 bytes = 512 KiB per CPU, allocated on `start()`.
pub const TRACE_CAP: usize = 32768;

pub const KIND_START: u8 = 0;
pub const KIND_END: u8 = 1;
/// Marker recorded by a DAG periodic reactor at the top of every period, so
/// the host can attribute execution intervals to period (job) indices.
pub const KIND_RELEASE: u8 = 2;

#[derive(Clone, Copy, Default)]
pub struct TraceEvent {
    /// Raw CPU counter value (TSC on x86).
    pub tsc: u64,
    pub task_id: u32,
    /// `KIND_START` or `KIND_END`.
    pub kind: u8,
}

static ENABLED: AtomicBool = AtomicBool::new(false);

static IDX: [AtomicUsize; NUM_MAX_CPU] = array![_ => AtomicUsize::new(0); NUM_MAX_CPU];

static mut BUFS: [Option<Vec<TraceEvent>>; NUM_MAX_CPU] = [const { None }; NUM_MAX_CPU];

static CAL_START_TSC: AtomicU64 = AtomicU64::new(0);
static CAL_START_US: AtomicU64 = AtomicU64::new(0);
static CAL_END_TSC: AtomicU64 = AtomicU64::new(0);
static CAL_END_US: AtomicU64 = AtomicU64::new(0);

/// Record one event.  Called from the task poll boundary in `task::run`.
///
/// Lock-free: only the current CPU writes to its own buffer, and the slot is
/// claimed atomically, so a preempting context on the same CPU cannot corrupt
/// an event nor deadlock.
#[inline]
pub(crate) fn record(task_id: u32, kind: u8) {
    if !ENABLED.load(Ordering::Acquire) {
        return;
    }

    let cpu_id = awkernel_lib::cpu::cpu_id();
    let i = IDX[cpu_id].fetch_add(1, Ordering::Relaxed);
    if i >= TRACE_CAP {
        return; // Buffer full: drop the event (counted via IDX overflow).
    }

    let tsc = awkernel_lib::delay::cpu_counter();

    unsafe {
        let bufs = &mut *core::ptr::addr_of_mut!(BUFS);
        if let Some(buf) = bufs[cpu_id].as_mut() {
            buf[i] = TraceEvent { tsc, task_id, kind };
        }
    }
}

/// Record a [`KIND_RELEASE`] marker for the task currently running on this
/// CPU.  Called from the DAG periodic reactor at the start of every period.
#[inline]
pub(crate) fn mark_release_current() {
    if !ENABLED.load(Ordering::Acquire) {
        return;
    }

    if let Some(task_id) = super::get_current_task(awkernel_lib::cpu::cpu_id()) {
        record(task_id, KIND_RELEASE);
    }
}

/// Allocate buffers (first call only), reset indices, take the start
/// calibration point, and enable recording.
pub fn start() {
    if ENABLED.load(Ordering::Acquire) {
        return;
    }

    let n = awkernel_lib::cpu::num_cpu();

    unsafe {
        let bufs = &mut *core::ptr::addr_of_mut!(BUFS);
        for buf in bufs.iter_mut().take(n) {
            if buf.is_none() {
                *buf = Some(alloc::vec![TraceEvent::default(); TRACE_CAP]);
            }
        }
    }

    for idx in IDX.iter().take(n) {
        idx.store(0, Ordering::Relaxed);
    }

    CAL_START_TSC.store(awkernel_lib::delay::cpu_counter(), Ordering::Relaxed);
    CAL_START_US.store(awkernel_lib::delay::uptime(), Ordering::Relaxed);

    // Buffers must be visible before any CPU starts recording.
    ENABLED.store(true, Ordering::Release);
}

/// Disable recording and take the end calibration point.
pub fn stop() {
    if !ENABLED.swap(false, Ordering::AcqRel) {
        return;
    }

    CAL_END_TSC.store(awkernel_lib::delay::cpu_counter(), Ordering::Relaxed);
    CAL_END_US.store(awkernel_lib::delay::uptime(), Ordering::Relaxed);
}

pub fn is_enabled() -> bool {
    ENABLED.load(Ordering::Acquire)
}

/// (start_tsc, start_us, end_tsc, end_us) for tick-to-time conversion.
pub fn calibration() -> (u64, u64, u64, u64) {
    (
        CAL_START_TSC.load(Ordering::Relaxed),
        CAL_START_US.load(Ordering::Relaxed),
        CAL_END_TSC.load(Ordering::Relaxed),
        CAL_END_US.load(Ordering::Relaxed),
    )
}

/// Number of events dropped on `cpu_id` because the buffer was full.
pub fn num_dropped(cpu_id: usize) -> usize {
    IDX[cpu_id].load(Ordering::Relaxed).saturating_sub(TRACE_CAP)
}

/// Copy of the recorded events on `cpu_id`.  Call only after `stop()`.
pub fn events(cpu_id: usize) -> Vec<TraceEvent> {
    let n = IDX[cpu_id].load(Ordering::Relaxed).min(TRACE_CAP);

    unsafe {
        let bufs = &*core::ptr::addr_of!(BUFS);
        match bufs[cpu_id].as_ref() {
            Some(buf) => buf[..n].to_vec(),
            None => Vec::new(),
        }
    }
}

/// Dump the recorded trace to the console in the `TRACE_*` CSV format
/// consumed by `awkernel_script/trace_view/plot_trace.py`.
///
/// Used both by the shell's `(trace)` command and by the boot-time
/// auto-trace task (real hardware, where no shell input is available:
/// the output is captured on the host with `minicom -C trace.log`).
pub fn dump_to_console() {
    use alloc::{format, string::String};
    use awkernel_lib::console;

    if is_enabled() {
        console::print("trace is running; stop it before dumping\r\n");
        return;
    }

    let (start_tsc, start_us, end_tsc, end_us) = calibration();
    if start_tsc == 0 {
        console::print("no trace recorded\r\n");
        return;
    }

    console::print("TRACE_BEGIN\r\n");
    console::print(&format!("TRACE_CAL,start,{start_tsc},{start_us}\r\n"));
    console::print(&format!("TRACE_CAL,end,{end_tsc},{end_us}\r\n"));

    // TRACE_TASK,<id>,<dag_id|->,<node_id|->,<cpu|cpu|...|->,<name>
    // dag/node identify the DAG membership, the cpu list is the task's
    // `cpu_set` (clustered tasks only).  `-` means "not applicable".
    for t in super::get_tasks() {
        let dag_info = {
            let mut node = awkernel_lib::sync::mutex::MCSNode::new();
            let info = t.info.lock(&mut node);
            info.get_dag_info()
        };
        let (dag_id, node_id) = match dag_info {
            Some(d) => (format!("{}", d.dag_id), format!("{}", d.node_id)),
            None => (String::from("-"), String::from("-")),
        };

        let cpus = match &t.cpu_set {
            Some(set) => {
                let mut s = String::new();
                for cpu in set.iter() {
                    if !s.is_empty() {
                        s.push('|');
                    }
                    s.push_str(&format!("{cpu}"));
                }
                s
            }
            None => String::from("-"),
        };

        console::print(&format!(
            "TRACE_TASK,{},{dag_id},{node_id},{cpus},{}\r\n",
            t.id, t.name
        ));
    }

    // TRACE_DAG,<dag_id>,<src_node_id>,<dst_node_id> — DAG topology, so the
    // host can compute critical paths from the log alone.
    for (dag_id, src, dst) in crate::dag::get_all_dag_edges() {
        console::print(&format!("TRACE_DAG,{dag_id},{src},{dst}\r\n"));
    }

    for cpu_id in 0..awkernel_lib::cpu::num_cpu() {
        let evs = events(cpu_id);
        let mut out = String::new();
        for e in &evs {
            let kind = match e.kind {
                KIND_START => 'S',
                KIND_END => 'E',
                _ => 'R',
            };
            out.push_str(&format!("TRACE_EV,{cpu_id},{},{kind},{}\r\n", e.task_id, e.tsc));

            // Flush in chunks so a single huge String is not required.
            if out.len() > 4096 {
                console::print(&out);
                out.clear();
            }
        }
        console::print(&out);

        // Expected line count so the host can detect serial data loss.
        console::print(&format!("TRACE_COUNT,{cpu_id},{}\r\n", evs.len()));

        let dropped = num_dropped(cpu_id);
        if dropped > 0 {
            console::print(&format!("TRACE_DROPPED,{cpu_id},{dropped}\r\n"));
        }
    }

    console::print("TRACE_END\r\n");
}
