union QUtil {
    s: [u16; 4],
    q: u64,
}

union LUtil {
    s: [u16; 2],
    l: u32,
}

/// Computes the checksum from three \u32\ arguments.
/// This function is typcially used for calculating the pseudo header checksum.
pub fn in_pseudo(a: u32, b: u32, c: u32) -> u16 {
    let sum64: u64 = a as u64 + b as u64 + c as u64;
    let q_util = QUtil { q: sum64 };
    let l_util;
    let mut sum;

    unsafe {
        l_util = LUtil {
            l: q_util.s[0] as u32 + q_util.s[1] as u32 + q_util.s[2] as u32 + q_util.s[3] as u32,
        };
        sum = l_util.s[0] as u32 + l_util.s[1] as u32;
    }
    if sum > 65535 {
        sum -= 65535;
    }
    sum as u16
}
