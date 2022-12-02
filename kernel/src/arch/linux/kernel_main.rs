use crate::board_info::BoardInfo;

#[start]
#[no_mangle]
extern "C" fn main(_argc: isize, _argv: *const *const u8) -> isize {
    if unsafe { super::heap::mmap() }.is_err() {
        let msg = b"failed to initialize heap memory\n";
        unsafe { libc::write(0, msg.as_ptr() as _, msg.len()) };
        return -1;
    };

    let board_info = BoardInfo::<()> { info: () };
    crate::main(&board_info);

    0
}
