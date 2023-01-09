use core::fmt::{Error, Write};
use log::Log;
use synctools::mcs::{MCSLock, MCSNode};

pub static CONSOLE: Console = Console::new();

pub struct Console {
    lock: MCSLock<StdOut>,
}

pub struct StdOut(());

impl Write for StdOut {
    fn write_str(&mut self, msg: &str) -> core::fmt::Result {
        let buf = msg.as_bytes();
        if unsafe { libc::write(0, buf.as_ptr() as _, buf.len()) } == 0 {
            Ok(())
        } else {
            Err(Error)
        }
    }
}

pub(crate) fn puts(msg: &str) {
    let mut node = MCSNode::new();
    let mut guard = CONSOLE.lock.lock(&mut node);
    let _ = guard.write_str(msg);
}

impl Console {
    const fn new() -> Self {
        Self {
            lock: MCSLock::new(StdOut(())),
        }
    }
}

impl Log for Console {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        if !self.enabled(record.metadata()) {
            return;
        }

        let mut node = MCSNode::new();
        let mut guard = self.lock.lock(&mut node);

        let stdout: &mut StdOut = &mut guard;
        crate::logger::write_msg(stdout, record);
    }

    fn flush(&self) {}
}

pub fn init() {
    let _ = log::set_logger(&CONSOLE);
    log::set_max_level(log::LevelFilter::Debug);
}
