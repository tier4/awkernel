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
use log::Level;

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
