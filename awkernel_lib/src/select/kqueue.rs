use awkernel_sync::{mcs::MCSNode, mutex::Mutex};
use core::{
    ptr::{null, null_mut},
    time::Duration,
};
use std::os::fd::RawFd;

use super::{EventFlag, EventType};

static FD_KQUEUE: Mutex<Option<RawFd>> = Mutex::new(None);

const KQUEUE_EVENT: usize = 1;

#[inline(always)]
fn kqueue_fd() -> RawFd {
    let mut node = MCSNode::new();
    let mut fd = FD_KQUEUE.lock(&mut node);

    if let Some(fd) = fd.as_ref() {
        *fd
    } else {
        let kq = unsafe { libc::kqueue() };
        assert!(kq != -1);

        // Add EVFILT_USER
        let kev = libc::kevent {
            ident: KQUEUE_EVENT, // user defined identifier
            filter: libc::EVFILT_USER,
            flags: libc::EV_ADD | libc::EV_ENABLE,
            fflags: 0,
            data: 0,
            udata: null_mut(),
        };

        let ret =
            unsafe { libc::kevent(kq, &kev as *const libc::kevent, 1, null_mut(), 0, null()) };
        assert!(ret != -1);

        *fd = Some(kq);
        kq
    }
}

pub(super) fn register_fd(raw_fd: RawFd) {
    let kq = kqueue_fd();

    let rev = libc::kevent {
        ident: raw_fd as libc::uintptr_t,
        filter: libc::EVFILT_READ,
        flags: libc::EV_ADD | libc::EV_DISABLE,
        fflags: 0,
        data: 0,
        udata: null_mut(),
    };

    let wev = libc::kevent {
        filter: libc::EVFILT_WRITE,
        ..rev
    };

    let ret = unsafe {
        libc::kevent(
            kq,
            &[rev, wev] as *const libc::kevent,
            2,
            null_mut(),
            0,
            null(),
        )
    };
    assert!(ret != -1);
}

pub(super) fn update_event(raw_fd: RawFd, event_flag: EventFlag) {
    let rev = libc::kevent {
        ident: raw_fd as libc::uintptr_t,
        filter: libc::EVFILT_READ,
        flags: if event_flag.contains(EventFlag::READ) {
            libc::EV_ENABLE
        } else {
            libc::EV_DISABLE
        },
        fflags: 0,
        data: 0,
        udata: null_mut(),
    };

    let wev = libc::kevent {
        filter: libc::EVFILT_WRITE,
        flags: if event_flag.contains(EventFlag::WRITE) {
            libc::EV_ENABLE
        } else {
            libc::EV_DISABLE
        },
        ..rev
    };

    let kq = kqueue_fd();
    let ret = unsafe {
        libc::kevent(
            kq,
            &[rev, wev] as *const libc::kevent,
            1,
            null_mut(),
            0,
            null(),
        )
    };
    assert!(ret != -1);
}

pub(super) fn notify() {
    let trigger_kev: libc::kevent = libc::kevent {
        ident: KQUEUE_EVENT,
        filter: libc::EVFILT_USER,
        flags: 0,
        fflags: libc::NOTE_TRIGGER,
        data: 0,
        udata: null_mut(),
    };

    let kq = kqueue_fd();
    let ret = unsafe {
        libc::kevent(
            kq,
            &trigger_kev as *const libc::kevent,
            1,
            null_mut(),
            0,
            null(),
        )
    };
    assert!(ret != -1);
}

pub(super) fn wait(timeout: Duration) {
    let timeout = libc::timespec {
        tv_sec: timeout.as_secs() as i64,
        tv_nsec: timeout.subsec_nanos() as i64,
    };

    let kq = kqueue_fd();

    let mut events: [libc::kevent; 32] = unsafe { std::mem::zeroed() };

    let nev = unsafe { libc::kevent(kq, null(), 0, events.as_mut_ptr(), 32, &timeout) };

    // Wake wakers.
    let mut i = 0;
    for event in events.iter() {
        i += 1;
        if i > nev as usize {
            break;
        }

        if event.filter == libc::EVFILT_READ {
            let raw_fd = event.ident as RawFd;
            disable_event(raw_fd, EventType::Read);

            {
                let mut node = MCSNode::new();
                let mut map = super::FD_TO_WAKER.lock(&mut node);
                map.remove(&(raw_fd, EventType::Read))
            }
            .map(|waker| waker.wake());
        }

        if event.filter == libc::EVFILT_WRITE {
            let raw_fd = event.ident as RawFd;
            disable_event(raw_fd, EventType::Write);

            {
                let mut node = MCSNode::new();
                let mut map = super::FD_TO_WAKER.lock(&mut node);
                map.remove(&(raw_fd, EventType::Write))
            }
            .map(|waker| waker.wake());
        }
    }
}

fn disable_event(raw_fd: RawFd, event: EventType) {
    let ev = libc::kevent {
        ident: raw_fd as libc::uintptr_t,
        filter: if event == EventType::Read {
            libc::EVFILT_READ
        } else {
            libc::EVFILT_WRITE
        },
        flags: libc::EV_DISABLE,
        fflags: 0,
        data: 0,
        udata: null_mut(),
    };

    let kq = kqueue_fd();
    let ret = unsafe { libc::kevent(kq, &ev as *const libc::kevent, 1, null_mut(), 0, null()) };
    assert!(ret != -1);
}
