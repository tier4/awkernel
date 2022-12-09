use core::fmt::Write;

use log::Level;

pub fn write_msg(writer: &mut impl Write, record: &log::Record) {
    let _ = writer.write_char('[');
    let _ = writer.write_str(record.level().as_str());
    let _ = writer.write_str("] ");

    match record.level() {
        Level::Info => {
            let msg = alloc::format!("{}\n", record.args());
            let _ = writer.write_str(msg.as_str());
        }
        _ => {
            if let (Some(file), Some(line)) = (record.file(), record.line()) {
                let msg = alloc::format!("{file}:{line}: {}\n", record.args());
                let _ = writer.write_str(msg.as_str());
            }
        }
    }
}
