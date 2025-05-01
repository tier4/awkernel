use awkernel_lib::file::FileManagerError;
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
        let file_handle = awkernel_lib::file::FileDescriptor::open_file(path)
            .or(Err(FileDescriptorError::FileDescriptionCreationError))?;

        FileOpener {
            file_handle: file_handle.clone(),
        }
        .await?;

        Ok(FileDescriptor { file_handle })
    }
}
pub struct FileOpener {
    file_handle: awkernel_lib::file::FileDescriptor,
}

impl Future for FileOpener {
    type Output = Result<(), FileDescriptorError>;
    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        match self.file_handle.open(cx.waker()) {
            Ok(true) => core::task::Poll::Ready(Ok(())),
            Ok(false) => core::task::Poll::Pending,
            Err(FileManagerError::InterfaceIsNotReady) => {
                core::task::Poll::Ready(Err(FileDescriptorError::InterfaceIsNotReady))
            }
            Err(_) => {
                core::task::Poll::Ready(Err(FileDescriptorError::FileDescriptionCreationError))
            }
        }
    }
}
