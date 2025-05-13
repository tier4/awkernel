#![no_std]

extern crate alloc;

use alloc::{collections::BTreeMap, format, string::String, sync::Arc, vec::Vec};
use awkernel_async_lib::{
    future::FutureExt, pubsub, scheduler::SchedulerType, select_biased, session_types::*,
};
use awkernel_lib::{
    file::{
        if_file::{FileSystemCmd, FileSystemCmdInfo, FileSystemWrapper, FileSystemWrapperError},
        FileManagerError, FileSystemResult,
    },
    heap::TALLOC,
    paging::{self, PAGESIZE},
    sync::{mcs::MCSNode, mutex::Mutex},
};
use core::{
    alloc::{GlobalAlloc, Layout},
    fmt,
    future::Future,
    task::Poll,
    time::Duration,
};
use fatfs::{
    format_volume, FileSystem, FormatVolumeOptions, FsOptions, IoBase, Read, Seek, SeekFrom, Write,
};

pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024; // 1MiB

pub async fn run() {
    let filesystem = FatfsInMemory {};
    awkernel_lib::file::add_interface(Arc::new(filesystem));
    let interface_id = 0;
    let Ok(layout) = Layout::from_size_align(MEMORY_FILESYSTEM_SIZE, PAGESIZE) else {
        panic!("Invalid layout")
    };

    let result = unsafe { TALLOC.alloc(layout) };
    if result.is_null() {
        panic!("NULL pointer");
    }

    let data =
        unsafe { Vec::from_raw_parts(result, MEMORY_FILESYSTEM_SIZE, MEMORY_FILESYSTEM_SIZE) };
    let mut disk = InMemoryDisk { data, position: 0 };
    let options = FormatVolumeOptions::new();
    if format_volume(&mut disk, options).is_ok() {
        log::info!("FAT filesystem formatted successfully in memory!");
    } else {
        log::info!("Error formatting!");
    }
    let fs = FileSystem::new(disk, FsOptions::new()).expect("Error creating file system");
    let root_dir = fs.root_dir();

    let mut fd_to_file = BTreeMap::new();
    loop {
        let mut wait_fs = FileSystemPolling {
            interface_id,
            wait: true,
        }
        .await;

        let Ok(cmdinfo) = awkernel_lib::file::cmd_queue_pop(interface_id) else {
            panic!("Wrong interface");
        };

        if let Some(cmdinfo) = cmdinfo {
            match cmdinfo.cmd {
                FileSystemCmd::OpenCmd => {
                    let ret;
                    match root_dir.open_file(&cmdinfo.path) {
                        Ok(file) => {
                            ret = Ok(FileSystemResult::Success);
                            fd_to_file.insert(cmdinfo.fd, file);
                        }
                        Err(e) => {
                            ret = Err(awkernel_lib::file::fatfs::FatFsError::OpenError);
                        }
                    };

                    awkernel_lib::file::fatfs::complete_file_operation(
                        interface_id,
                        cmdinfo.fd,
                        ret,
                    );
                }
                FileSystemCmd::CreateCmd => {}
                FileSystemCmd::ReadCmd => {}
                FileSystemCmd::WriteCmd => {}
                FileSystemCmd::SeekCmd => {}
            }
        }
    }
}

struct FileSystemPolling {
    interface_id: u64,
    wait: bool,
}

impl Future for FileSystemPolling {
    type Output = Result<(), FileManagerError>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let m = self.get_mut();

        if !m.wait {
            return Poll::Ready(Ok(()));
        }

        m.wait = false;

        match awkernel_lib::file::register_waker_for_fs(m.interface_id, cx.waker().clone()) {
            Ok(true) => Poll::Pending,
            Ok(false) => Poll::Ready(Ok(())),
            Err(e) => Poll::Ready(Err(e)),
        }
    }
}
