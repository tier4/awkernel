use crate::sync::{mcs::MCSNode, mutex::Mutex};
use bitflags::bitflags;
use core::{
    ptr::{null, null_mut},
    task::Waker,
    time::Duration,
};
use std::{collections::BTreeMap, os::fd::RawFd};

static FD_TO_WAKER: Mutex<BTreeMap<(RawFd, EventType), Waker>> = Mutex::new(BTreeMap::new());

static FD_EPOLL: Mutex<Option<RawFd>> = Mutex::new(None);
static FD_EVENT: Mutex<Option<RawFd>> = Mutex::new(None);

pub struct FdWaker {
    raw_fd: RawFd,
    events: EventFlag,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum EventType {
    Read,
    Write,
}

bitflags! {
    pub struct EventFlag: u32 {
        const READ = 1 << 0;
        const WRITE = 1 << 1;
    }
}

impl FdWaker {
    pub fn new(raw_fd: RawFd) -> Self {
        // Register the event.
        let mut event = libc::epoll_event {
            events: 0,
            u64: raw_fd as u64,
        };

        let epfd = epoll_fd();
        let result = unsafe { libc::epoll_ctl(epfd, libc::EPOLL_CTL_ADD, raw_fd, &mut event) };
        assert_eq!(result, 0);

        // Create.
        Self {
            raw_fd,
            events: EventFlag::empty(),
        }
    }

    /// Register `waker` of `self.raw_fd`.
    /// After invoking `waker.wake()`, the waker is cleared.
    pub fn register_waker(&mut self, waker: Waker, ev_type: EventType) {
        // Analysis `ev_type`.
        match ev_type {
            EventType::Read => self.events.insert(EventFlag::READ),
            EventType::Write => self.events.insert(EventFlag::WRITE),
            _ => (),
        }

        let mut events = 0;

        if self.events.contains(EventFlag::READ) {
            events |= libc::EPOLLIN as u32;
        }

        if self.events.contains(EventFlag::WRITE) {
            events |= libc::EPOLLOUT as u32;
        }

        let mut event = libc::epoll_event {
            events,
            u64: self.raw_fd as u64,
        };

        // Update the event.
        let epfd = epoll_fd();
        let result = unsafe { libc::epoll_ctl(epfd, libc::EPOLL_CTL_MOD, self.raw_fd, &mut event) };
        assert_eq!(result, 0);

        // Register the waker.
        {
            let mut node = MCSNode::new();
            let mut map = FD_TO_WAKER.lock(&mut node);
            map.insert((self.raw_fd, ev_type), waker);
        }
    }
}

impl Drop for FdWaker {
    fn drop(&mut self) {
        let epfd = epoll_fd();
        unsafe { libc::epoll_ctl(epfd, libc::EPOLL_CTL_DEL, self.raw_fd, null_mut()) };

        {
            let mut node = MCSNode::new();
            let mut map = FD_TO_WAKER.lock(&mut node);

            if self.events.contains(EventFlag::READ) {
                map.remove(&(self.raw_fd, EventType::Read));
            }

            if self.events.contains(EventFlag::WRITE) {
                map.remove(&(self.raw_fd, EventType::Write));
            }
        }
    }
}

/// Wait events and invoke wakers if necessary.
pub fn wait(timeout: Duration) {
    let epfd = epoll_fd();
    let mut events = [libc::epoll_event { events: 0, u64: 0 }; 32];

    let timeout = libc::timespec {
        tv_sec: timeout.as_secs() as i64,
        tv_nsec: timeout.subsec_nanos() as i64,
    };

    // Wait events.
    let result = unsafe { libc::epoll_pwait2(epfd, events.as_mut_ptr(), 32, &timeout, null()) };
    assert!(result != -1);
    if result == 0 {
        return;
    }

    let mut node = MCSNode::new();
    let mut map = FD_TO_WAKER.lock(&mut node);

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
            map.remove(&(raw_fd, EventType::Read))
                .map(|waker| waker.clone().wake());
        }

        if event.events & libc::EPOLLOUT as u32 != 0 {
            map.remove(&(raw_fd, EventType::Write))
                .map(|waker| waker.clone().wake());
        }
    }
}

/// Send an even to a task which is calling `poll()`.
pub fn notify() {
    let buf = [1u64; 1];
    let evfd = event_fd();

    unsafe { libc::write(evfd, buf.as_ptr() as *const _, core::mem::size_of::<i64>()) };
}

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
        let epfd = unsafe { libc::epoll_create(1) }; // size argument is ignored since Linux 2.6.8
        if epfd == -1 {
            panic!("failed epoll_fd()");
        }

        // Get the event descriptor.
        let evfd = event_fd();

        // Register the event.
        let mut event = libc::epoll_event {
            events: libc::EPOLLIN as u32,
            u64: evfd as u64,
        };

        let result = unsafe { libc::epoll_ctl(epfd, libc::EPOLL_CTL_ADD, evfd, &mut event) };
        assert!(result == 0);

        *fd = Some(epfd);
        epfd
    }
}
