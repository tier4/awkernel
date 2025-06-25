//! The async filesystem trait definitions needed to implement new async virtual filesystems
use super::path::AsyncVfsPath;
use crate::time::Time;
use alloc::{boxed::Box, string::String};
use async_trait::async_trait;
use awkernel_lib::file::{
    error::{Error, IoError},
    io::SeekFrom,
    vfs::error::{VfsError, VfsErrorKind, VfsResult},
    vfs::path::VfsMetadata,
};
use core::fmt::Debug;
use core::pin::Pin;
use embedded_io_async::{Read, Seek, Write};
use futures::stream::{BoxStream, Stream};
use futures::Future;
/// File system implementations must implement this trait
/// All path parameters are absolute, starting with '/', except for the root directory
/// which is simply the empty string (i.e. "")
/// The character '/' is used to delimit directories on all platforms.
/// Path components may be any UTF-8 string, except "/", "." and ".."
///
/// Please use the test_macros [test_macros::test_async_vfs!] and [test_macros::test_async_vfs_readonly!]
pub trait AsyncFileSystem: Sync + Send + Clone + 'static {
    /// このファイルシステムが返すエラー型。
    type Error: IoError + Clone + Send + Sync + Debug;

    /// open_file から返される読み取り可能なファイルオブジェクトの型。
    /// この型は embedded_io_async::Read と embedded_io_async::Seek を実装し、
    /// Send と 'static のライフタイム要件を満たす必要があります。
    type ReadFile: Read<Error = Error<Self::Error>>
        + Seek<Error = Error<Self::Error>>
        + Send
        + Unpin
        + 'static;

    /// create_file から返される書き込み可能なファイルオブジェクトの型。
    /// この型は embedded_io_async::Write と embedded_io_async::Seek を実装し、
    /// Send と 'static のライフタイム要件を満たす必要があります。
    type WriteFile: Write<Error = Error<Self::Error>>
        + Seek<Error = Error<Self::Error>>
        + Send
        + Unpin
        + 'static;

    /// このディレクトリパスの直下の子をすべてイテレートします。
    /// NOTE: 返される String アイテムは、ローカルのファイル名（"/" を含まない）です。
    fn read_dir(
        &self,
        path: &str,
    ) -> impl Future<
        Output = VfsResult<
            Pin<Box<dyn Stream<Item = String> + Send + Unpin + 'static>>,
            Self::Error,
        >,
    > + Send;

    /// このパスにディレクトリを作成します。
    ///
    /// 親ディレクトリはすでに存在している必要があります。
    async fn create_dir(&self, path: &str) -> VfsResult<(), Self::Error>;

    /// このパスのファイルを読み取り用に開きます。
    async fn open_file(&self, path: &str) -> VfsResult<Self::ReadFile, Self::Error>;

    /// このパスにファイルを書き込み用に作成します。
    async fn create_file(&self, path: &str) -> VfsResult<Self::WriteFile, Self::Error>;

    /// このパスのファイルを追記用に開きます。
    async fn append_file(&self, path: &str) -> VfsResult<Self::WriteFile, Self::Error>;

    /// このパスのファイルのメタデータを返します。
    fn metadata(
        &self,
        path: &str,
    ) -> impl Future<Output = VfsResult<VfsMetadata, Self::Error>> + Send;

    /// ファイルの作成タイムスタンプを設定します（実装がサポートしている場合）。
    async fn set_creation_time(&self, _path: &str, _time: Time) -> VfsResult<(), Self::Error> {
        Err(VfsErrorKind::NotSupported.into())
    }
    /// ファイルの変更タイムスタンプを設定します（実装がサポートしている場合）。
    async fn set_modification_time(&self, _path: &str, _time: Time) -> VfsResult<(), Self::Error> {
        Err(VfsErrorKind::NotSupported.into())
    }
    /// ファイルのアクセスタイムスタンプを設定します（実装がサポートしている場合）。
    async fn set_access_time(&self, _path: &str, _time: Time) -> VfsResult<(), Self::Error> {
        Err(VfsErrorKind::NotSupported.into())
    }
    /// パスにファイルまたはディレクトリが存在する場合は true を、それ以外の場合は false を返します。
    async fn exists(&self, path: &str) -> VfsResult<bool, Self::Error>;

    /// このパスのファイルを削除します。
    async fn remove_file(&self, path: &str) -> VfsResult<(), Self::Error>;

    /// このパスのディレクトリを削除します。
    async fn remove_dir(&self, path: &str) -> VfsResult<(), Self::Error>;

    /// 同一ファイルシステム内で src パスを dest パスにコピーします（オプション）。
    async fn copy_file(&self, _src: &str, _dest: &str) -> VfsResult<(), Self::Error> {
        Err(VfsErrorKind::NotSupported.into())
    }
    /// 同一ファイルシステム内で src パスを dest パスに移動します（オプション）。
    async fn move_file(&self, _src: &str, _dest: &str) -> VfsResult<(), Self::Error> {
        Err(VfsErrorKind::NotSupported.into())
    }
    /// 同一ファイルシステム内で src ディレクトリを dest パスに移動します（オプション）。
    async fn move_dir(&self, _src: &str, _dest: &str) -> VfsResult<(), Self::Error> {
        Err(VfsErrorKind::NotSupported.into())
    }
}
