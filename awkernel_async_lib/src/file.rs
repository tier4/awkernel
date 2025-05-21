use awkernel_lib::file::if_file::FileSystemWrapperError;
use futures::Future;
use pin_project::pin_project;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileDescriptorError {
    FileDescriptionCreationError,
    WriteError,
    InterfaceIsNotReady,
}

#[derive(Clone)]
pub struct FileDescriptor {
    file_handle: awkernel_lib::file::FileDescriptor,
}

impl FileDescriptor {
    pub async fn open(path: &str) -> Result<FileDescriptor, FileDescriptorError> {
        let file_handle = awkernel_lib::file::FileDescriptor::new(path)
            .or(Err(FileDescriptorError::FileDescriptionCreationError))?;

        file_handle
            .filesystem
            .open(file_handle.interface_id, file_handle.fd, &file_handle.path);

        FileOpenWaiter {
            file_handle: file_handle.clone(),
        }
        .await?;

        Ok(FileDescriptor { file_handle })
    }
    pub async fn create(path: &str) -> Result<FileDescriptor, FileDescriptorError> {
        let file_handle = awkernel_lib::file::FileDescriptor::new(path)
            .or(Err(FileDescriptorError::FileDescriptionCreationError))?;

        file_handle
            .filesystem
            .create(file_handle.interface_id, file_handle.fd, &file_handle.path);

        FileCreateWaiter {
            file_handle: file_handle.clone(),
        }
        .await?;

        Ok(FileDescriptor { file_handle })
    }

    pub async fn read(&self, buf: &mut [u8]) -> Result<usize, FileDescriptorError> {
        self.file_handle.filesystem.read(
            self.file_handle.interface_id,
            self.file_handle.fd,
            buf.len(),
        );

        FileReader {
            file_handle: self.file_handle.clone(),
            buf,
        }
        .await
    }

    pub async fn write(&self, buf: &[u8]) -> Result<usize, FileDescriptorError> {
        self.file_handle
            .filesystem
            .write(self.file_handle.interface_id, self.file_handle.fd, buf);

        FileWriter {
            file_handle: self.file_handle.clone(),
        }
        .await
    }
}

#[pin_project]
pub struct FileOpenWaiter {
    file_handle: awkernel_lib::file::FileDescriptor,
}

impl Future for FileOpenWaiter {
    type Output = Result<(), FileDescriptorError>;
    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let this = self.project();

        match this.file_handle.filesystem.open_wait(
            this.file_handle.interface_id,
            this.file_handle.fd,
            cx.waker(),
        ) {
            Ok(true) => core::task::Poll::Ready(Ok(())),
            Ok(false) => core::task::Poll::Pending,
            Err(FileSystemWrapperError::OpenError) => {
                core::task::Poll::Ready(Err(FileDescriptorError::InterfaceIsNotReady))
            }
            Err(_) => {
                core::task::Poll::Ready(Err(FileDescriptorError::FileDescriptionCreationError))
            }
        }
    }
}

#[pin_project]
pub struct FileCreateWaiter {
    file_handle: awkernel_lib::file::FileDescriptor,
}

impl Future for FileCreateWaiter {
    type Output = Result<(), FileDescriptorError>;
    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let this = self.project();

        match this.file_handle.filesystem.create_wait(
            this.file_handle.interface_id,
            this.file_handle.fd,
            cx.waker(),
        ) {
            Ok(true) => core::task::Poll::Ready(Ok(())),
            Ok(false) => core::task::Poll::Pending,
            Err(FileSystemWrapperError::OpenError) => {
                core::task::Poll::Ready(Err(FileDescriptorError::InterfaceIsNotReady))
            }
            Err(_) => {
                core::task::Poll::Ready(Err(FileDescriptorError::FileDescriptionCreationError))
            }
        }
    }
}

#[pin_project]
pub struct FileReader<'a> {
    file_handle: awkernel_lib::file::FileDescriptor,
    buf: &'a mut [u8],
}

impl Future for FileReader<'_> {
    type Output = Result<usize, FileDescriptorError>;
    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let this = self.project();

        match this.file_handle.filesystem.read_wait(
            this.file_handle.interface_id,
            this.file_handle.fd,
            this.buf,
            cx.waker(),
        ) {
            Ok(Some(size)) => core::task::Poll::Ready(Ok(size)),
            Ok(None) => core::task::Poll::Pending,
            Err(FileSystemWrapperError::ReadError) => {
                core::task::Poll::Ready(Err(FileDescriptorError::InterfaceIsNotReady))
            }
            Err(_) => {
                core::task::Poll::Ready(Err(FileDescriptorError::FileDescriptionCreationError))
            }
        }
    }
}

#[pin_project]
pub struct FileWriter {
    file_handle: awkernel_lib::file::FileDescriptor,
}

impl Future for FileWriter {
    type Output = Result<usize, FileDescriptorError>;
    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let this = self.project();

        match this.file_handle.filesystem.write_wait(
            this.file_handle.interface_id,
            this.file_handle.fd,
            cx.waker(),
        ) {
            Ok(Some(size)) => core::task::Poll::Ready(Ok(size)),
            Ok(None) => core::task::Poll::Pending,
            Err(FileSystemWrapperError::ReadError) => {
                core::task::Poll::Ready(Err(FileDescriptorError::InterfaceIsNotReady))
            }
            Err(_) => {
                core::task::Poll::Ready(Err(FileDescriptorError::FileDescriptionCreationError))
            }
        }
    }
}
