use crate::{heap::TALLOC, paging::PAGESIZE, sync::rwlock::RwLock};
use alloc::{collections::BTreeMap, string::String, vec::Vec};
use core::{
    alloc::{GlobalAlloc, Layout},
    fmt,
};
use fatfs::{
    format_volume, FileSystem, FormatVolumeOptions, FsOptions, IoBase, LossyOemCpConverter,
    NullTimeProvider, Read, Seek, SeekFrom, Write,
};

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
