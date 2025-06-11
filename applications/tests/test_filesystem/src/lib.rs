#![no_std]

extern crate alloc;
use awkernel_async_lib::file::FileDescriptor;
use awkernel_lib::file::io::SeekFrom;
use core::str;

pub async fn run() {
    awkernel_async_lib::spawn(
        "test filesystem".into(),
        filesystem_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn filesystem_test() {
    let fd = match FileDescriptor::create("a.txt").await {
        Ok(fd) => fd,
        Err(e) => {
            log::error!("Failed to open a file - a.txt: {e:?}");
            return;
        }
    };

    let data_to_write = b"Hello World!";
    match fd.write(data_to_write).await {
        Ok(w_bytes) => {
            log::info!("write bytes:{w_bytes}");
        }
        Err(e) => {
            log::error!("Error write file: {e:?}");
            return;
        }
    };

    let _ = fd.seek(SeekFrom::Start(0)).await;

    let mut buf = [0_u8; 13];
    let read_bytes = match fd.read(&mut buf).await {
        Ok(r_bytes) => {
            log::info!("read bytes:{r_bytes}");
            r_bytes
        }
        Err(e) => {
            log::error!("Error read file: {e:?}");
            return;
        }
    };

    match str::from_utf8(&buf[..read_bytes]) {
        Ok(s) => log::info!("read result:{s}"),
        Err(_) => log::error!("read result doesn't match the written content."),
    }
}
