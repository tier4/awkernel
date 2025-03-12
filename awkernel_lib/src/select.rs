use crate::sync::{mcs::MCSNode, mutex::Mutex};
use bitflags::bitflags;
use core::{task::Waker, time::Duration};
use std::{collections::BTreeMap, os::fd::RawFd};

#[cfg(target_os = "linux")]
mod epoll;

#[cfg(any(
    target_os = "macos",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd"
))]
mod kqueue;

static FD_TO_WAKER: Mutex<BTreeMap<(RawFd, EventType), Waker>> = Mutex::new(BTreeMap::new());

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
    #[derive(Clone, Copy)]
    pub struct EventFlag: u32 {
        const READ = 1 << 0;
        const WRITE = 1 << 1;
    }
}

impl FdWaker {
    pub fn new(raw_fd: RawFd) -> Self {
        // Register the event.
        register_fd(raw_fd);

        // Create.
        Self {
            raw_fd,
            events: EventFlag::empty(),
        }
    }

    /// Register `waker` of `self.raw_fd`.
    /// After invoking `waker.wake()`, the waker is cleared.
    pub fn register_waker(&mut self, waker: Waker, ev_type: EventType) {
        // Add the event.
        match ev_type {
            EventType::Read => self.events.insert(EventFlag::READ),
            EventType::Write => self.events.insert(EventFlag::WRITE),
        }

        // Update the event.
        update_event(self.raw_fd, self.events);

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
#[inline(always)]
pub fn wait(timeout: Duration) {
    #[cfg(target_os = "linux")]
    epoll::wait(timeout);

    #[cfg(any(
        target_os = "macos",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd"
    ))]
    kqueue::wait(timeout);
}

/// Send an even to a task which is calling `poll()`.
#[inline(always)]
pub fn notify() {
    #[cfg(target_os = "linux")]
    epoll::notify();

    #[cfg(any(
        target_os = "macos",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd"
    ))]
    kqueue::notify();
}

#[inline(always)]
fn update_event(raw_fd: RawFd, events: EventFlag) {
    #[cfg(target_os = "linux")]
    epoll::update_event(raw_fd, events);

    #[cfg(any(
        target_os = "macos",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd"
    ))]
    kqueue::update_event(raw_fd, events);
}

#[inline(always)]
fn register_fd(raw_fd: RawFd) {
    #[cfg(target_os = "linux")]
    epoll::register_fd(raw_fd);

    #[cfg(any(
        target_os = "macos",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd"
    ))]
    kqueue::register_fd(raw_fd);
}
