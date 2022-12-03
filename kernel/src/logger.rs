use core::fmt::Write;

pub fn write_msg(writer: &mut impl Write, record: &log::Record) {
    let _ = writer.write_char('[');
    let _ = writer.write_str(record.level().as_str());
    let _ = writer.write_str("] ");

    let msg = alloc::format!("{}\n", record.args());
    let _ = writer.write_str(msg.as_str());
}
