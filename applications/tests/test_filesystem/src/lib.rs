#![no_std]

extern crate alloc;

use alloc::vec::Vec;
use awkernel_lib::file::{init_filesystem, FileDescriptor};

pub async fn run() {
    awkernel_async_lib::spawn(
        "test filesystem".into(),
        filesystem_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn filesystem_test() {
    init_filesystem();

    log::info!("okay!!!");

    let w_bytes;
    {
        let fd = match FileDescriptor::create_file("file.txt") {
            Ok(file) => file,
            Err(e) => panic!("Error create file: {:?}", e),
        };

        let data_to_write = b"Hello World!";
        w_bytes = match fd.write_file(data_to_write) {
            Ok(w_bytes) => w_bytes,
            Err(e) => panic!("Error write file: {:?}", e),
        };
    }

    {
        let fd = match FileDescriptor::open_file("file.txt") {
            Ok(file) => file,
            Err(e) => panic!("Error create file: {:?}", e),
        };

        let mut buf = Vec::new();
        buf.resize(w_bytes, 0);
        let _ = match fd.read_file(&mut buf) {
            Ok(w_bytes) => w_bytes,
            Err(e) => panic!("Erro write file: {:?}", e),
        };

        match core::str::from_utf8(&buf) {
            Ok(s) => log::info!("file.txt content: {}", s),
            Err(_) => log::info!("Error converting to string"),
        }
    }
}
