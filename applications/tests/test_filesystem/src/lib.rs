#![no_std]

extern crate alloc;

use alloc::vec::Vec;
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
    let fd = match awkernel_async_lib::file::FileDescriptor::create("a.txt").await {
        Ok(fd) => fd,
        Err(e) => {
            panic!("Failed to open a file - a.txt: {:?}", e);
        }
    };

    log::info!("fd:{}", fd.fd);

    //let data_to_write = b"Hello World!";
    //let _ = match fd.write(data_to_write).await {
    //Ok(w_bytes) => {
    //log::info!("write bytes:{}", w_bytes);
    //}
    //Err(e) => panic!("Error write files"),
    //};

    //let _ = fd.seek(SeekFrom::Start(0)).await;

    //let mut buf = [0_u8; 13];
    //let read_bytes = match fd.read(&mut buf).await {
    //Ok(r_bytes) => {
    //log::info!("read bytes:{}", r_bytes);
    //r_bytes
    //}
    //Err(e) => panic!("Erro read file: {:?}", e),
    //};

    //match str::from_utf8(&buf[..read_bytes]) {
    //Ok(s) => log::info!("read result:{}", s),
    //Err(_) => panic!("read result panic"),
    //}
}
