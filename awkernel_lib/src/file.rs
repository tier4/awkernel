use crate::{heap::TALLOC, paging::PAGESIZE, sync::rwlock::RwLock};
use alloc::{string::String, vec::Vec};
use core::{
    alloc::{GlobalAlloc, Layout},
    fmt,
};
use fatfs::{
    format_volume, FileSystem, FormatVolumeOptions, FsOptions, IoBase, Read, Seek, SeekFrom, Write,
};

pub static FILE_MANAGER: RwLock<Option<FileManager>> = RwLock::new(None);

pub const MEMORY_FILESYSTEM_START: usize = 0;
pub const MEMORY_FILESYSTEM_SIZE: usize = 1024 * 1024; // 1MiB

pub struct FileManager {
    fs: FileSystem<InMemoryDisk>,
}

struct InMemoryDisk {
    data: Vec<u8>,
    position: u64,
}

pub fn init_filesystem() {
    let Ok(layout) = Layout::from_size_align(MEMORY_FILESYSTEM_SIZE, PAGESIZE) else {
        panic!("Invalid layout")
    };

    let result = unsafe { TALLOC.alloc(layout) };
    if result.is_null() {
        panic!("NULL pointer");
    }

    let data =
        unsafe { Vec::from_raw_parts(result, MEMORY_FILESYSTEM_SIZE, MEMORY_FILESYSTEM_SIZE) };
    let disk = InMemoryDisk { data, position: 0 };

    let options = FormatVolumeOptions::new();

    let mut mutable_disk = disk;
    if format_volume(&mut mutable_disk, options).is_ok() {
        log::info!("FAT filesystem formatted successfully in memory!");
    } else {
        log::info!("Error formatting!");
    }

    let fs = FileSystem::new(mutable_disk, FsOptions::new()).expect("Error creating file system");

    let mut file_manager = FILE_MANAGER.write();
    *file_manager = Some(FileManager { fs });
}

impl IoBase for InMemoryDisk {
    type Error = InMemoryDiskError;
}

impl Read for InMemoryDisk {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        let len = core::cmp::min(buf.len(), (self.data.len() as u64 - self.position) as usize);
        if len == 0 {
            return Ok(0);
        }
        buf[..len]
            .copy_from_slice(&self.data[self.position as usize..self.position as usize + len]);
        self.position += len as u64;
        Ok(len)
    }
}

impl Write for InMemoryDisk {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        let len = core::cmp::min(buf.len(), (self.data.len() as u64 - self.position) as usize);
        if len == 0 {
            return Ok(0);
        }
        self.data[self.position as usize..self.position as usize + len]
            .copy_from_slice(&buf[..len]);
        self.position += len as u64;
        Ok(len)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(()) // In-memory, nothing to flush
    }
}

impl Seek for InMemoryDisk {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error> {
        let new_position = match pos {
            SeekFrom::Start(offset) => offset as i64,
            SeekFrom::Current(offset) => self.position as i64 + offset,
            SeekFrom::End(offset) => self.data.len() as i64 + offset,
        };

        if new_position < 0 || new_position > self.data.len() as i64 {
            return Err(InMemoryDiskError::OutOfBounds);
        }

        self.position = new_position as u64;
        Ok(self.position)
    }
}

#[derive(Debug)]
pub enum InMemoryDiskError {
    OutOfBounds,
    WriteZero,
    UnexpectedEof,
    Interrupted,
    Other(String),
}

impl fmt::Display for InMemoryDiskError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InMemoryDiskError::OutOfBounds => write!(f, "Out of bounds access"),
            InMemoryDiskError::WriteZero => write!(f, "Failed to write whole buffer"),
            InMemoryDiskError::UnexpectedEof => write!(f, "Failed to fill whole buffer"),
            InMemoryDiskError::Interrupted => write!(f, "Operation interrupted"),
            InMemoryDiskError::Other(msg) => write!(f, "An error occurred: {}", msg),
        }
    }
}

impl fatfs::IoError for InMemoryDiskError {
    fn is_interrupted(&self) -> bool {
        match self {
            InMemoryDiskError::Interrupted => true,
            _ => false,
        }
    }

    fn new_unexpected_eof_error() -> Self {
        InMemoryDiskError::UnexpectedEof
    }

    fn new_write_zero_error() -> Self {
        InMemoryDiskError::WriteZero
    }
}

pub struct FileDescriptor {
    // Note first_cluster is None if file is empty
    first_cluster: Option<u32>,
    // Note: if offset points between clusters current_cluster is the previous cluster
    current_cluster: Option<u32>,
    // current position in this file
    offset: u32,
    // file dir entry editor - None for root dir
    entry: Option<fatfs::dir_entry::DirEntryEditor>,
}

#[derive(Debug)]
pub enum FileManagerError {
    OpenError,
    CreateError,
    ReadError,
    WriteError,
    SeekError,
}

impl fmt::Display for FileManagerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FileManagerError::OpenError => write!(f, "Open failed"),
            FileManagerError::CreateError => write!(f, "Create failed"),
            FileManagerError::ReadError => write!(f, "Read failed"),
            FileManagerError::WriteError => write!(f, "Write failed"),
            FileManagerError::SeekError => write!(f, "Seek failed"),
        }
    }
}

impl FileDescriptor {
    pub fn open_file(path: &str) -> Result<Self, FileManagerError> {
        let file_manager = FILE_MANAGER.read();
        let fs;
        if let Some(fm) = &*file_manager {
            fs = &fm.fs;
        } else {
            panic!("file_manager isn't initialized");
        }

        let root_dir = fs.root_dir();
        let result;
        if let Ok(file) = root_dir.open_file(path) {
            result = Ok(FileDescriptor {
                first_cluster: file.first_cluster,
                current_cluster: file.current_cluster,
                offset: file.offset,
                entry: file.entry.clone(),
            })
        } else {
            result = Err(FileManagerError::OpenError)
        }
        result
    }

    pub fn create_file(path: &str) -> Result<Self, FileManagerError> {
        let file_manager = FILE_MANAGER.read();
        let fs;
        if let Some(fm) = &*file_manager {
            fs = &fm.fs;
        } else {
            panic!("file_manager isn't initialized");
        }

        let root_dir = fs.root_dir();
        let result;
        if let Ok(file) = root_dir.create_file(path) {
            result = Ok(FileDescriptor {
                first_cluster: file.first_cluster,
                current_cluster: file.current_cluster,
                offset: file.offset,
                entry: file.entry.clone(),
            })
        } else {
            result = Err(FileManagerError::CreateError)
        }
        result
    }

    pub fn read_file(self, buf: &mut [u8]) -> Result<usize, FileManagerError> {
        let mut file_manager = FILE_MANAGER.write();
        let fs;
        if let Some(fm) = &mut *file_manager {
            fs = &fm.fs;
        } else {
            panic!("file_manager isn't initialized");
        }

        let mut file = fatfs::File {
            first_cluster: self.first_cluster,
            current_cluster: self.current_cluster,
            offset: self.offset,
            entry: self.entry,
            fs,
        };

        file.read(buf).map_err(|_| FileManagerError::ReadError)
    }

    pub fn write_file(self, buf: &[u8]) -> Result<usize, FileManagerError> {
        let mut file_manager = FILE_MANAGER.write();
        let fs;
        if let Some(fm) = &mut *file_manager {
            fs = &fm.fs;
        } else {
            panic!("file_manager isn't initialized");
        }

        let mut file = fatfs::File {
            first_cluster: self.first_cluster,
            current_cluster: self.current_cluster,
            offset: self.offset,
            entry: self.entry,
            fs,
        };

        return file.write(buf).map_err(|_| FileManagerError::WriteError);
    }
}
