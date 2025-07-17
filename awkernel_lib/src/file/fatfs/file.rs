//! FAT filesystem file implementation.
//!
//! # Concurrency Limitations
//!
//! The FAT filesystem was not designed for concurrent access. While this implementation
//! provides some consistency guarantees through shared metadata and atomic operations,
//! there are inherent limitations:
//!
//! ## Known Limitations:
//!
//! 1. **Byte-Level Write Interleaving**: Multiple concurrent writers to the same file
//!    may have their writes interleaved at the byte level within a cluster.
//!
//! 2. **No Transactional Guarantees**: Operations like file extension (allocating new
//!    clusters and updating size) are not fully transactional. A crash or error during
//!    these operations may leave the file in an inconsistent state.

use alloc::sync::Arc;
use core::convert::TryFrom;
use core::fmt::Debug;

use super::super::io::{IoBase, Read, Seek, SeekFrom, Write};
use super::dir_entry::DirEntryEditor;
use super::error::Error;
use super::fs::{FileSystem, ReadWriteSeek};
use super::time::{Date, DateTime, TimeProvider};

use awkernel_sync::{mcs::MCSNode, mutex::Mutex};

const MAX_FILE_SIZE: u32 = u32::MAX;

/// A FAT filesystem file object used for reading and writing data.
///
/// This struct is created by the `open_file` or `create_file` methods on `Dir`.
pub struct File<IO: ReadWriteSeek + Send + Debug, TP, OCC> {
    // Shared metadata for this file (None for root dir)
    metadata: Option<Arc<Mutex<DirEntryEditor>>>,
    // current position in this file
    offset: u32,
    // file-system reference
    fs: Arc<FileSystem<IO, TP, OCC>>,
}

/// An extent containing a file's data on disk.
///
/// This is created by the `extents` method on `File`, and represents
/// a byte range on the disk that contains a file's data. All values
/// are in bytes.
#[derive(Clone, Debug)]
pub struct Extent {
    pub offset: u64,
    pub size: u32,
}

impl<IO: ReadWriteSeek + Send + Debug, TP, OCC> File<IO, TP, OCC> {
    pub(crate) fn new(
        metadata: Option<Arc<Mutex<DirEntryEditor>>>,
        fs: Arc<FileSystem<IO, TP, OCC>>,
    ) -> Self {
        File {
            metadata,
            fs,
            offset: 0,
        }
    }

    /// Truncate file in current position.
    ///
    /// # Errors
    ///
    /// `Error::Io` will be returned if the underlying storage object returned an I/O error.
    ///
    /// # Panics
    ///
    /// Will panic if this is the root directory.
    pub fn truncate(&mut self) -> Result<(), Error<IO::Error>> {
        log::trace!("File::truncate");
        if let Some(ref metadata_arc) = self.metadata {
            // IMPORTANT: We hold the metadata lock during the entire truncate operation
            // to ensure atomicity. Lock ordering: metadata → disk
            let mut node = MCSNode::new();
            let mut metadata = metadata_arc.lock(&mut node);

            metadata.set_size(self.offset);
            if self.offset == 0 {
                metadata.set_first_cluster(None, self.fs.fat_type());
            }

            let first_cluster = metadata.inner().first_cluster(self.fs.fat_type());

            let current_cluster = self.get_current_cluster_with_metadata(&metadata)?;

            if let Some(cluster) = current_cluster {
                // current cluster is none only if offset is 0
                debug_assert!(self.offset > 0);
                FileSystem::truncate_cluster_chain(&self.fs, cluster)
            } else {
                debug_assert!(self.offset == 0);
                if let Some(n) = first_cluster {
                    FileSystem::free_cluster_chain(&self.fs, n)?;
                }
                Ok(())
            }
        } else {
            panic!("Trying to truncate a file without metadata (root directory?)");
        }
    }

    /// Get the extents of a file on disk.
    ///
    /// This returns an iterator over the byte ranges on-disk occupied by
    /// this file.
    pub fn extents(&mut self) -> impl Iterator<Item = Result<Extent, Error<IO::Error>>> + '_ {
        let fs = &self.fs;
        let cluster_size = fs.cluster_size();
        let Some(mut bytes_left) = self.size() else {
            return None.into_iter().flatten();
        };
        let first_cluster = if let Some(ref metadata_arc) = self.metadata {
            let mut node = MCSNode::new();
            let metadata = metadata_arc.lock(&mut node);
            metadata.inner().first_cluster(self.fs.fat_type())
        } else {
            None
        };
        let Some(first) = first_cluster else {
            return None.into_iter().flatten();
        };

        Some(
            core::iter::once(Ok(first))
                .chain(FileSystem::cluster_iter(fs, first))
                .map(move |cluster_err| match cluster_err {
                    Ok(cluster) => {
                        let size = cluster_size.min(bytes_left);
                        bytes_left -= size;
                        Ok(Extent {
                            offset: fs.offset_from_cluster(cluster),
                            size,
                        })
                    }
                    Err(e) => Err(e),
                }),
        )
        .into_iter()
        .flatten()
    }

    pub(crate) fn abs_pos(&self) -> Option<u64> {
        // Returns current position relative to filesystem start
        // Note: when between clusters it returns position after previous cluster
        match self.get_current_cluster().ok()? {
            Some(n) => {
                let cluster_size = self.fs.cluster_size();
                let offset_mod_cluster_size = self.offset % cluster_size;
                let offset_in_cluster = if offset_mod_cluster_size == 0 {
                    // position points between clusters - we are returning previous cluster so
                    // offset must be set to the cluster size
                    cluster_size
                } else {
                    offset_mod_cluster_size
                };
                let offset_in_fs = self.fs.offset_from_cluster(n) + u64::from(offset_in_cluster);
                Some(offset_in_fs)
            }
            None => None,
        }
    }

    fn flush_dir_entry(&mut self) -> Result<(), Error<IO::Error>> {
        if let Some(ref metadata_arc) = self.metadata {
            let mut node = MCSNode::new();
            let mut metadata = metadata_arc.lock(&mut node);
            metadata.flush(&self.fs)?;
        }
        Ok(())
    }

    /// Sets date and time of creation for this file.
    ///
    /// Note: it is set to a value from the `TimeProvider` when creating a file.
    #[deprecated]
    pub fn set_created(&mut self, date_time: DateTime) {
        if let Some(ref metadata_arc) = self.metadata {
            let mut node = MCSNode::new();
            let mut metadata = metadata_arc.lock(&mut node);
            metadata.set_created(date_time);
        }
    }

    /// Sets date of last access for this file.
    ///
    /// Note: it is overwritten by a value from the `TimeProvider` on every file read operation.
    #[deprecated]
    pub fn set_accessed(&mut self, date: Date) {
        if let Some(ref metadata_arc) = self.metadata {
            let mut node = MCSNode::new();
            let mut metadata = metadata_arc.lock(&mut node);
            metadata.set_accessed(date);
        }
    }

    /// Sets date and time of last modification for this file.
    ///
    /// Note: it is overwritten by a value from the `TimeProvider` on every file write operation.
    #[deprecated]
    pub fn set_modified(&mut self, date_time: DateTime) {
        if let Some(ref metadata_arc) = self.metadata {
            let mut node = MCSNode::new();
            let mut metadata = metadata_arc.lock(&mut node);
            metadata.set_modified(date_time);
        }
    }

    fn size(&self) -> Option<u32> {
        if let Some(ref metadata_arc) = self.metadata {
            let mut node = MCSNode::new();
            let metadata = metadata_arc.lock(&mut node);
            metadata.inner().size()
        } else {
            None
        }
    }

    fn is_dir(&self) -> bool {
        if let Some(ref metadata_arc) = self.metadata {
            let mut node = MCSNode::new();
            let metadata = metadata_arc.lock(&mut node);
            metadata.inner().is_dir()
        } else {
            true // root directory
        }
    }

    pub(crate) fn first_cluster(&self) -> Option<u32> {
        if let Some(ref metadata_arc) = self.metadata {
            let mut node = MCSNode::new();
            let metadata = metadata_arc.lock(&mut node);
            metadata.inner().first_cluster(self.fs.fat_type())
        } else {
            None
        }
    }

    /// Calculate current cluster with an existing metadata lock held.
    fn get_current_cluster_with_metadata(
        &self,
        metadata: &impl core::ops::Deref<Target = DirEntryEditor>,
    ) -> Result<Option<u32>, Error<IO::Error>> {
        if self.offset == 0 {
            return Ok(None);
        }

        let Some(first_cluster) = metadata.inner().first_cluster(self.fs.fat_type()) else {
            return Ok(None); // empty file
        };

        let offset_in_clusters = self.fs.clusters_from_bytes(u64::from(self.offset));
        debug_assert!(offset_in_clusters > 0);

        let clusters_to_skip = offset_in_clusters - 1;
        let mut cluster = first_cluster;
        let mut iter = FileSystem::cluster_iter(&self.fs, first_cluster);

        for _i in 0..clusters_to_skip {
            cluster = if let Some(r) = iter.next() {
                r?
            } else {
                // cluster chain ends before the current position
                return Err(Error::CorruptedFileSystem);
            };
        }

        Ok(Some(cluster))
    }

    /// Get the cluster that contains the current file position.
    ///
    /// Special case: when offset is at a cluster boundary (offset % cluster_size == 0),
    /// this returns the PREVIOUS cluster, not the next one.
    fn get_current_cluster(&self) -> Result<Option<u32>, Error<IO::Error>> {
        if self.offset == 0 {
            return Ok(None);
        }

        if let Some(ref metadata_arc) = self.metadata {
            let mut node = MCSNode::new();
            let metadata = metadata_arc.lock(&mut node);
            self.get_current_cluster_with_metadata(&metadata)
        } else {
            Ok(None)
        }
    }

    fn flush(&mut self) -> Result<(), Error<IO::Error>> {
        self.flush_dir_entry()?;
        let mut node = MCSNode::new();
        let mut disk_guard = self.fs.disk.lock(&mut node);
        disk_guard.flush()?;
        Ok(())
    }

    pub(crate) fn is_root_dir(&self) -> bool {
        self.metadata.is_none()
    }
}

impl<IO: ReadWriteSeek + Send + Debug, TP: TimeProvider, OCC> File<IO, TP, OCC> {
    fn update_dir_entry_after_write(&mut self) {
        let offset = self.offset;
        if let Some(ref metadata_arc) = self.metadata {
            let mut node = MCSNode::new();
            let mut metadata = metadata_arc.lock(&mut node);
            let now = self.fs.options.time_provider.get_current_date_time();
            metadata.set_modified(now);
            if metadata.inner().size().is_some_and(|s| offset > s) {
                metadata.set_size(offset);
            }
        }
    }
}

impl<IO: ReadWriteSeek + Send + Debug, TP, OCC> Drop for File<IO, TP, OCC> {
    fn drop(&mut self) {
        if let Err(err) = self.flush() {
            log::error!("flush failed {err:?}");
        }

        if let Some(metadata_arc) = self.metadata.take() {
            let mut node = MCSNode::new();
            let metadata = metadata_arc.lock(&mut node);
            let entry_pos = metadata.pos;
            drop(metadata);
            drop(metadata_arc);
            self.fs.cleanup_metadata_if_unused(entry_pos);
        }
    }
}

// Note: derive cannot be used because of invalid bounds. See: https://github.com/rust-lang/rust/issues/26925
impl<IO: ReadWriteSeek + Send + Debug, TP, OCC> Clone for File<IO, TP, OCC> {
    fn clone(&self) -> Self {
        File {
            metadata: self.metadata.clone(),
            offset: self.offset,
            fs: Arc::clone(&self.fs),
        }
    }
}

impl<IO: ReadWriteSeek + Send + Debug, TP, OCC> IoBase for File<IO, TP, OCC> {
    type Error = Error<IO::Error>;
}

impl<IO: ReadWriteSeek + Send + Debug, TP: TimeProvider, OCC> Read for File<IO, TP, OCC> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        log::trace!("File::read");
        let cluster_size = self.fs.cluster_size();

        // Hold metadata lock during entire read operation to prevent truncate races
        // Lock ordering: metadata → disk
        if let Some(ref metadata_arc) = self.metadata {
            let mut node = MCSNode::new();
            let mut metadata = metadata_arc.lock(&mut node);

            let current_cluster_opt = if self.offset % cluster_size == 0 {
                // next cluster
                match self.get_current_cluster_with_metadata(&metadata)? {
                    None => {
                        if self.offset == 0 {
                            metadata.inner().first_cluster(self.fs.fat_type())
                        } else {
                            None
                        }
                    }
                    Some(n) => {
                        let r = FileSystem::cluster_iter(&self.fs, n).next();
                        match r {
                            Some(Err(err)) => return Err(err),
                            Some(Ok(n)) => Some(n),
                            None => None,
                        }
                    }
                }
            } else {
                self.get_current_cluster_with_metadata(&metadata)?
            };

            let Some(current_cluster) = current_cluster_opt else {
                return Ok(0);
            };

            let size = metadata.inner().size();
            if let Some(s) = size {
                if self.offset >= s {
                    return Ok(0);
                }
            }
            let offset_in_cluster = self.offset % cluster_size;
            let bytes_left_in_cluster = (cluster_size - offset_in_cluster) as usize;
            let bytes_left_in_file = size
                .map(|s| (s - self.offset) as usize)
                .unwrap_or(bytes_left_in_cluster);
            let read_size = buf.len().min(bytes_left_in_cluster).min(bytes_left_in_file);
            if read_size == 0 {
                return Ok(0);
            }

            log::trace!("read {read_size} bytes in cluster {current_cluster}");
            let offset_in_fs =
                self.fs.offset_from_cluster(current_cluster) + u64::from(offset_in_cluster);

            // lock ordering: metadata → disk
            let read_bytes = {
                let mut node_disk = MCSNode::new();
                let mut disk_guard = self.fs.disk.lock(&mut node_disk);
                disk_guard.seek(SeekFrom::Start(offset_in_fs))?;
                disk_guard.read(&mut buf[..read_size])?
            };

            if read_bytes == 0 {
                return Ok(0);
            }

            self.offset += read_bytes as u32;

            if self.fs.options.update_accessed_date {
                let now = self.fs.options.time_provider.get_current_date();
                metadata.set_accessed(now);
            }

            Ok(read_bytes)
        } else {
            unreachable!("Root directory should not be a file");
        }
    }
}

impl<IO: ReadWriteSeek + Send + Debug, TP: TimeProvider, OCC> Write for File<IO, TP, OCC> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        log::trace!("File::write");
        let cluster_size = self.fs.cluster_size();
        let offset_in_cluster = self.offset % cluster_size;
        let bytes_left_in_cluster = (cluster_size - offset_in_cluster) as usize;
        let bytes_left_until_max_file_size = (MAX_FILE_SIZE - self.offset) as usize;
        let write_size = buf
            .len()
            .min(bytes_left_in_cluster)
            .min(bytes_left_until_max_file_size);
        // Exit early if we are going to write no data
        if write_size == 0 {
            return Ok(0);
        }
        // Mark the volume 'dirty'
        self.fs.set_dirty_flag(true)?;
        // Get cluster for write possibly allocating new one
        let current_cluster = if self.offset % cluster_size == 0 {
            // next cluster
            let next_cluster = match self.get_current_cluster()? {
                None => {
                    if self.offset == 0 {
                        self.first_cluster()
                    } else {
                        None
                    }
                }
                Some(n) => {
                    let r = FileSystem::cluster_iter(&self.fs, n).next();
                    match r {
                        Some(Err(err)) => return Err(err),
                        Some(Ok(n)) => Some(n),
                        None => None,
                    }
                }
            };

            if let Some(n) = next_cluster {
                n
            } else {
                // end of chain reached - allocate new cluster
                if self.first_cluster().is_none() {
                    if let Some(ref metadata_arc) = self.metadata {
                        // IMPORTANT: Lock ordering - metadata held while calling alloc_cluster internally acquires: fs_info, disk (one each)
                        let mut node = MCSNode::new();
                        let mut metadata = metadata_arc.lock(&mut node);
                        // Double-check under lock in case another thread allocated first cluster
                        if metadata.inner().first_cluster(self.fs.fat_type()).is_none() {
                            let new_cluster =
                                FileSystem::alloc_cluster(&self.fs, None, self.is_dir())?;
                            log::trace!("allocated first cluster {new_cluster}");
                            metadata.set_first_cluster(Some(new_cluster), self.fs.fat_type());
                            new_cluster
                        } else {
                            // Another thread allocated first cluster, try again
                            drop(metadata);
                            return self.write(buf);
                        }
                    } else {
                        unreachable!("Root directory should not be a file");
                    }
                } else {
                    let new_cluster = FileSystem::alloc_cluster(
                        &self.fs,
                        self.get_current_cluster()?,
                        self.is_dir(),
                    )?;
                    log::trace!("allocated cluster {new_cluster}");
                    new_cluster
                }
            }
        } else {
            match self.get_current_cluster()? {
                Some(n) => n,
                None => panic!("Offset inside cluster but no cluster allocated"),
            }
        };
        log::trace!("write {write_size} bytes in cluster {current_cluster}");
        let offset_in_fs =
            self.fs.offset_from_cluster(current_cluster) + u64::from(offset_in_cluster);
        let written_bytes = {
            let mut node = MCSNode::new();
            let mut disk_guard = self.fs.disk.lock(&mut node);
            disk_guard.seek(SeekFrom::Start(offset_in_fs))?;
            disk_guard.write(&buf[..write_size])?
        };
        if written_bytes == 0 {
            return Ok(0);
        }
        // some bytes were writter - update position and optionally size
        self.offset += written_bytes as u32;
        self.update_dir_entry_after_write();
        Ok(written_bytes)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Self::flush(self)
    }
}

impl<IO: ReadWriteSeek + Send + Debug, TP, OCC> Seek for File<IO, TP, OCC> {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error> {
        log::trace!("File::seek");
        let size_opt = self.size();
        let new_offset_opt: Option<u32> = match pos {
            SeekFrom::Current(x) => i64::from(self.offset)
                .checked_add(x)
                .and_then(|n| u32::try_from(n).ok()),
            SeekFrom::Start(x) => u32::try_from(x).ok(),
            SeekFrom::End(o) => size_opt
                .and_then(|s| i64::from(s).checked_add(o))
                .and_then(|n| u32::try_from(n).ok()),
        };
        let Some(mut new_offset) = new_offset_opt else {
            log::error!("Invalid seek offset");
            return Err(Error::InvalidInput);
        };

        if let Some(size) = size_opt {
            if new_offset > size {
                log::warn!("Seek beyond the end of the file");
                new_offset = size;
            }
        }

        if new_offset > 0 {
            if let Some(ref metadata_arc) = self.metadata {
                let mut node = MCSNode::new();
                let metadata = metadata_arc.lock(&mut node);
                let first_cluster = metadata.inner().first_cluster(self.fs.fat_type());

                if let Some(first) = first_cluster {
                    // Calculate how many clusters are needed for the target offset
                    let offset_in_clusters = self.fs.clusters_from_bytes(u64::from(new_offset));
                    if offset_in_clusters > 0 {
                        let clusters_to_skip = offset_in_clusters - 1;
                        let mut _cluster = first;
                        let mut iter = FileSystem::cluster_iter(&self.fs, first);

                        for i in 0..clusters_to_skip {
                            _cluster = if let Some(r) = iter.next() {
                                r?
                            } else {
                                // Cluster chain ends before the new position seek to the end of the last cluster
                                new_offset = self.fs.bytes_from_clusters(i + 1) as u32;
                                break;
                            };
                        }
                    }
                } else {
                    // empty file - always seek to 0
                    new_offset = 0;
                }
            }
        }

        self.offset = new_offset;
        Ok(u64::from(self.offset))
    }
}
