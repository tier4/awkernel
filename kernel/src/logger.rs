use core::fmt::Write;
use log::Level;
use t4os_lib::delay;

pub fn write_msg(writer: &mut impl Write, record: &log::Record) {
    let usec = delay::uptime();
    let time = alloc::format!("[{:>13} ", usec / 1000);

    let _ = writer.write_str(time.as_str());
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
