use core::ptr::{read_volatile, write_volatile};
use super::mbox::MboxChannel;

const MBOX_REQUEST: u32 = 0;
const MBOX_CHANNEL_PROP: u32 = 8;
const MBOX_TAG_LAST: u32 = 0;

/// Framebuffer settings
pub struct FramebufferInfo {
    pub width: u32,
    pub height: u32,
    pub pitch: u32,
    pub is_rgb: bool,
    pub framebuffer: *mut u32,
}

/// Initializes the linear framebuffer
pub fn lfb_init(channel: &MboxChannel) -> Result<FramebufferInfo, &'static str> {
    log::info!("lfb_init 1");
    let mut mbox = [0u32; 35];
    mbox[0] = 35 * 4;
    mbox[1] = MBOX_REQUEST;

    mbox[2] = 0x48003; // Set physical width and height
    mbox[3] = 8;
    mbox[4] = 8;
    mbox[5] = 1024; // Width
    mbox[6] = 768;  // Height

    mbox[7] = 0x48004; // Set virtual width and height
    mbox[8] = 8;
    mbox[9] = 8;
    mbox[10] = 1024; // Virtual width
    mbox[11] = 768;  // Virtual height

    mbox[12] = 0x48009; // Set virtual offset
    mbox[13] = 8;
    mbox[14] = 8;
    mbox[15] = 0; // X offset
    mbox[16] = 0; // Y offset

    mbox[17] = 0x48005; // Set depth
    mbox[18] = 4;
    mbox[19] = 4;
    mbox[20] = 32; // Depth

    mbox[21] = 0x48006; // Set pixel order
    mbox[22] = 4;
    mbox[23] = 4;
    mbox[24] = 1; // RGB

    mbox[25] = 0x40001; // Get framebuffer
    mbox[26] = 8;
    mbox[27] = 8;
    mbox[28] = 4096; // Pointer
    mbox[29] = 0;    // Size

    mbox[30] = 0x40008; // Get pitch
    mbox[31] = 4;
    mbox[32] = 4;
    mbox[33] = 0; // Pitch

    mbox[34] = MBOX_TAG_LAST;

    if channel.mbox_call(&mut mbox) && mbox[20] == 32 && mbox[28] != 0 {
        log::info!(" mbox[28] 0x{:016x}",  mbox[28]);
        let framebuffer_address = mbox[28] & 0x3FFFFFFF; // Convert GPU address to ARM address
        log::info!("framebuffer_address: 0x{:016x}", framebuffer_address);
        let width = mbox[5]; // Get actual physical width
        let height = mbox[6]; // Get actual physical height
        let pitch = mbox[33]; // Get number of bytes per row
        let is_rgb = mbox[24] == 1; // Get actual color order

        Ok(FramebufferInfo {
            width,
            height,
            pitch,
            is_rgb,
            framebuffer: framebuffer_address as *mut u32,
        })
    } else {
        Err("Unable to set screen resolution to 1024x768x32")
    }
}

/// Show a picture on the linear framebuffer
pub fn lfb_showpicture(fb_info: &FramebufferInfo) {
    let character = [
        0x00, 0x00, 0x7E, 0x42, 0x42, 0x42, 0x7E, 0x00
    ]; // Example character

    let x = 100;
    let y = 100;
    let mut framebuffer = fb_info.framebuffer;
    log::info!("lfb_showpicture");
    for j in 0..8 {
        for i in 0..8 {
            let pixel = (character[j] >> (7 - i)) & 1;
            log::info!("lfb_showpicture2");
            let color = if pixel == 1 { 0xFFFFFF } else { 0x000000 };
            log::info!("lfb_showpicture3");
            let index = (y + j) * (fb_info.pitch as usize / 4) + (x + i);
            log::info!(" index{:}", index);
            log::info!("lfb_showpicture4");

            unsafe { write_volatile(framebuffer.offset(index as isize), color) }; // Write the color to the framebuffer
            log::info!("lfb_showpicture5");
        }
    }
}


