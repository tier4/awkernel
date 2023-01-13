pub fn uptime() -> u64 {
    t4os_lib::delay::uptime()
}

pub fn wait_microsec(usec: u64) {
    t4os_lib::delay::wait_microsec(usec)
}
