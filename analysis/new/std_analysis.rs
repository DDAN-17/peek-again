#[no_mangle]
pub fn std_analysis(bytes: &[u8]) -> impl Iterator<Item = &u8> {
    let mut iter = bytes.into_iter().peekable();
    iter.next_if(|x| *x == &69);
    iter
}
