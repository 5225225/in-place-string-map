use in_place_string_map::MapInPlace;

fn decode_percent(s: &mut str) -> &mut str {
    let mut m = MapInPlace::new(s);

    while let Some(c) = m.pop() {
        match c {
            '%' => {
                let num = m.pop_chars(2).expect("not enough chars");
                let n = u8::from_str_radix(num, 16).expect("invalid hex");
                m.push(n as char).expect("no more capacity");
            }
            _ => {
                m.push(c).expect("no more capacity");
            }
        }
    }

    m.into_mapped()
}

fn main() {
    let mut percent = "abc%64%65fg".to_string();
    let mapped_percent = decode_percent(&mut percent);
    assert_eq!(mapped_percent, "abcdefg");
}
