const STOEPLITZ_KEYSEED: u16 = 0x6d5a;

pub fn stoeplitz_to_key(key: &mut [u8]) {
    let skey = STOEPLITZ_KEYSEED.to_be();

    assert_eq!(key.len() % 2, 0);

    for i in (0..key.len()).step_by(2) {
        key[i] = (skey >> 8) as u8;
        key[i + 1] = skey as u8;
    }
}
