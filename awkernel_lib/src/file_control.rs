pub fn set_nonblocking(fd: libc::c_int) -> Result<(), std::io::Error> {
    // Get the current flag.
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if flags == -1 {
        return Err(std::io::Error::last_os_error());
    }

    // Make it non-blocking.
    let ret = unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) };
    if ret == -1 {
        return Err(std::io::Error::last_os_error());
    }

    Ok(())
}
