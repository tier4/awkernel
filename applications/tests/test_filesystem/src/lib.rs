#![no_std]

extern crate alloc;

use alloc::{string::String, vec::Vec};
use awkernel_lib::{
    file::{init_file_manager, FILE_MANAGER},
    sync::mcs::MCSNode,
};

use fatfs::{Read, Seek, SeekFrom, Write};

pub async fn run() {
    awkernel_async_lib::spawn(
        "test filesystem".into(),
        filesystem_test(),
        awkernel_async_lib::scheduler::SchedulerType::FIFO,
    )
    .await;
}

async fn filesystem_test() {
    init_file_manager();

    let root_dir = file_manager.unwrap().fs.root_dir();
    let w_bytes;
    {
        let mut file = match root_dir.create_file("file.txt") {
            Ok(file) => file,
            Err(e) => panic!("Error create file: {:?}", e),
        };

        let data_to_write = b"Hello World!";
        w_bytes = match file.write(data_to_write) {
            Ok(w_bytes) => w_bytes,
            Err(e) => panic!("Erro write file: {:?}", e),
        };
    }

    {
        let mut file = match root_dir.open_file("file.txt") {
            Ok(file) => file,
            Err(e) => panic!("Error open file: {:?}", e),
        };
        let mut buf = Vec::new();
        buf.resize(w_bytes, 0);
        let _ = match file.read(&mut buf) {
            Ok(r_bytes) => r_bytes,
            Err(e) => panic!("Erro read file: {:?}", e),
        };

        match core::str::from_utf8(&buf) {
            Ok(s) => log::info!("file.txt content: {}", s),
            Err(_) => log::info!("Error converting to string"),
        }
    }
}
