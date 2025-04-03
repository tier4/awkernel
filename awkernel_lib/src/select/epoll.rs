use awkernel_sync::{mcs::MCSNode, mutex::Mutex};
use core::{ptr::null, time::Duration};
use std::os::fd::RawFd;

use crate::select::{EventFlag, EventType};

static FD_EPOLL: Mutex<Option<RawFd>> = Mutex::new(None);

static FD_EVENT: Mutex<Option<RawFd>> = Mutex::new(None);

/// The maximum number of events that an `epoll()` call can handle.
/// If you want to handle more events, increase this value.
const NUM_EPOLL_EVENT: usize = 32;

#[inline(always)]
fn event_fd() -> RawFd {
    let mut node = MCSNode::new();
    let mut fd = FD_EVENT.lock(&mut node);

    if let Some(fd) = fd.as_ref() {
        *fd
    } else {
        let evfd = unsafe { libc::eventfd(0, 0) };
        assert!(evfd != -1);

        *fd = Some(evfd);
        evfd
    }
}

/// Get the file descriptor of epoll.
#[inline(always)]
fn epoll_fd() -> RawFd {
    let mut node = MCSNode::new();
    let mut fd = FD_EPOLL.lock(&mut node);

    if let Some(fd) = fd.as_ref() {
        *fd
    } else {
        // Create epoll, and register an event fd and the standard input.
        let epfd = unsafe { libc::epoll_create(1) }; // size argument is ignored since Linux 2.6.8
        assert!(epfd != -1);

        register_event_fd(epfd);
        register_stdin_fd(epfd);

        *fd = Some(epfd);
        epfd
    }
}

fn register_event_fd(epfd: RawFd) {
    // Get the event descriptor.
    let evfd = event_fd();

    // Register the event.
    let mut event = libc::epoll_event {
        events: libc::EPOLLIN as u32,
        u64: evfd as u64,
    };
    let result = unsafe { libc::epoll_ctl(epfd, libc::EPOLL_CTL_ADD, evfd, &mut event) };
    assert!(result == 0);
}

fn register_stdin_fd(epfd: RawFd) {
    // Register the standard input.
    let mut event = libc::epoll_event {
        events: libc::EPOLLIN as u32,
        u64: libc::STDIN_FILENO as u64,
    };
    let result =
        unsafe { libc::epoll_ctl(epfd, libc::EPOLL_CTL_ADD, libc::STDIN_FILENO, &mut event) };
    assert!(result == 0);
}

pub(super) fn register_fd(raw_fd: RawFd) {
    let mut event = libc::epoll_event {
        events: 0,
        u64: raw_fd as u64,
    };

    let epfd = epoll_fd();
    let result = unsafe { libc::epoll_ctl(epfd, libc::EPOLL_CTL_ADD, raw_fd, &mut event) };
    assert_eq!(result, 0);
}

pub(super) fn update_event(raw_fd: RawFd, event_flag: EventFlag) {
    let mut events = 0;

    if event_flag.contains(EventFlag::READ) {
        events |= libc::EPOLLIN as u32;
    }

    if event_flag.contains(EventFlag::WRITE) {
        events |= libc::EPOLLOUT as u32;
    }

    let mut event = libc::epoll_event {
        events,
        u64: raw_fd as u64,
    };

    // Update the event.
    let epfd = epoll_fd();
    let result = unsafe { libc::epoll_ctl(epfd, libc::EPOLL_CTL_MOD, raw_fd, &mut event) };
    assert_eq!(result, 0);
}

pub(super) fn wait(timeout: Duration) {
    let evfd = event_fd();
    let epfd = epoll_fd();
    let mut events = [libc::epoll_event { events: 0, u64: 0 }; NUM_EPOLL_EVENT];

    let timeout = libc::timespec {
        tv_sec: timeout.as_secs() as i64,
        tv_nsec: timeout.subsec_nanos() as i64,
    };

    // Wait events.
    let result = unsafe {
        libc::epoll_pwait2(
            epfd,
            events.as_mut_ptr(),
            NUM_EPOLL_EVENT as i32,
            &timeout,
            null(),
        )
    };
    assert!(result != -1);
    if result == 0 {
        return;
    }

    // Wake wakers.
    let mut i = 0;
    for event in events.iter() {
        i += 1;
        if i > result as usize {
            break;
        }

        if event.events == 0 {
            continue;
        }

        let raw_fd = event.u64 as RawFd;

        if event.events & libc::EPOLLIN as u32 != 0 {
            if event.u64 == evfd as u64 {
                let buf = [0u64; 1];
                let result = unsafe {
                    libc::read(evfd, buf.as_ptr() as *mut _, core::mem::size_of::<i64>())
                };
                assert!(result != -1);
            } else if let Some(waker) = {
                let mut node = MCSNode::new();
                let mut map = super::FD_TO_WAKER.lock(&mut node);
                map.remove(&(raw_fd, EventType::Read))
            } {
                waker.wake();
            }
        }

        if event.events & libc::EPOLLOUT as u32 != 0 {
            if let Some(waker) = {
                let mut node = MCSNode::new();
                let mut map = super::FD_TO_WAKER.lock(&mut node);
                map.remove(&(raw_fd, EventType::Write))
            } {
                waker.wake();
            }
        }

        // Update epoll.
        let mut events = EventFlag::empty();
        {
            let mut node = MCSNode::new();
            let map = super::FD_TO_WAKER.lock(&mut node);
            if map.contains_key(&(raw_fd, EventType::Read)) {
                events.insert(EventFlag::READ);
            }

            if map.contains_key(&(raw_fd, EventType::Write)) {
                events.insert(EventFlag::WRITE);
            }
        }

        update_event(raw_fd, events);
    }
}

pub(super) fn notify() {
    let buf = [1u64; 1];
    let evfd = event_fd();
    unsafe { libc::write(evfd, buf.as_ptr() as *const _, core::mem::size_of::<i64>()) };
}
