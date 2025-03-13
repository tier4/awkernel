//! This module defines how to print logging messages.
//!
//! # Example
//!
//! ```
//! use log;
//!
//! log::info!("Hello, world!");
//! log::debug!("This is a debug message.");
//! log::error!("This is an error message.");
//! log::trace!("This is a trace message.");
//! ```

use crate::{console::Console, delay};
use log::{Level, Log};

#[cfg(not(feature = "std"))]
use alloc::string::String;

static mut LOGGER: Logger = Logger {
    raw_console: None,
    buf_console: None,
};

/// Format a logging message and print it out.
pub fn write_msg(writer: &mut dyn Console, record: &log::Record) {
    let usec = delay::uptime();
    let time = alloc::format!("[{:>13} ", usec / 1000);

    let _ = writer.write_str(time.as_str());
    let _ = writer.write_str(record.level().as_str());
    let _ = writer.write_str("] ");

    match record.level() {
        Level::Info => {
            let msg = alloc::format!("{}\r\n", record.args());
            let _ = writer.write_str(msg.as_str());
        }
        _ => {
            if let (Some(file), Some(line)) = (record.file(), record.line()) {
                let msg = alloc::format!("{file}:{line}: {}\r\n", record.args());
                let _ = writer.write_str(msg.as_str());
            }
        }
    }
}

/// Format a logging message.
pub fn format_msg(record: &log::Record) -> String {
    let usec = delay::uptime();
    let head = alloc::format!("[{:>13} {}] ", usec / 1000, record.level().as_str());

    match record.level() {
        Level::Info => {
            alloc::format!("{head}{}\r\n", record.args())
        }
        _ => {
            if let (Some(file), Some(line)) = (record.file(), record.line()) {
                alloc::format!("{head}{file}:{line}: {}\r\n", record.args())
            } else {
                alloc::format!("{head}{}\r\n", record.args())
            }
        }
    }
}

struct Logger {
    raw_console: Option<&'static dyn Log>,
    buf_console: Option<&'static dyn Log>,
}

impl Log for Logger {
    fn enabled(&self, metadata: &log::Metadata) -> bool {
        if let Some(log) = self.buf_console {
            log.enabled(metadata)
        } else if let Some(log) = self.raw_console {
            log.enabled(metadata)
        } else {
            false
        }
    }

    fn log(&self, record: &log::Record) {
        if let Some(log) = self.buf_console {
            log.log(record);
        } else if let Some(log) = self.raw_console {
            log.log(record);
        }
    }

    fn flush(&self) {
        if let Some(log) = self.buf_console {
            log.flush();
        } else if let Some(log) = self.raw_console {
            log.flush();
        }
    }
}

pub fn set_raw_console(logger: &'static dyn Log) {
    let ptr = &raw mut LOGGER;
    unsafe {
        (*ptr).raw_console = Some(logger);
    }
}

pub fn set_buf_console(logger: &'static dyn Log) {
    let ptr = &raw mut LOGGER;
    unsafe {
        (*ptr).buf_console = Some(logger);
    }
}

/// Initialize the logger.
///
/// # Safety
///
/// This function must be called once.
pub unsafe fn init() {
    let ptr = &raw const LOGGER;
    unsafe {
        let _ = log::set_logger(&*ptr);
    }
}
