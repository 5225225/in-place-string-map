struct MapInPlace<'a> {
    buf: &'a mut String,
    mapped_head: usize,
    unmapped_head: usize,
}

impl std::ops::Drop for MapInPlace<'_> {
    fn drop(&mut self) {
        self.buf.truncate(self.mapped_head - 1);
    }
}

fn map_in_place<'a>(s: &'a mut String) -> MapInPlace<'a> {
    MapInPlace {
        buf: s,
        mapped_head: 0,
        unmapped_head: 0,
    }
}

impl MapInPlace<'_> {
    fn mapped(&self) -> &str {
        &self.buf[0..self.mapped_head]
    }

    fn unmapped(&self) -> &str {
        &self.buf[self.unmapped_head..]
    }

    /// Pushes a character onto the end of the mapped portion
    fn push(&mut self, ch: char) {
        let chlen = ch.len_utf8();
        assert!(
            self.mapped_head <= self.unmapped_head,
            "Tried to overtake unmapped head!"
        );
        match chlen {
            1 => unsafe { self.buf.as_mut_vec()[self.mapped_head] = ch as u8 },
            l => {
                let mut tempbuf = [0_u8; 4_usize];
                let sbytes = ch.encode_utf8(&mut tempbuf).as_bytes();
                unsafe {
                    self.buf.as_mut_vec()[self.mapped_head..self.mapped_head + l]
                        .copy_from_slice(sbytes);
                }
            }
        }
        self.mapped_head += chlen;
    }

    /// Pops a character from the start of the unmapped portion
    fn pop(&mut self) -> Option<char> {
        let ch = self.unmapped().chars().next()?;

        self.unmapped_head += ch.len_utf8();

        Some(ch)
    }

    /// Pops a character from the start of the unmapped portion
    fn pop_chars(&mut self, n: usize) -> Option<&str> {
        let (to_take, _) = self.unmapped().char_indices().take(n + 1).last()?;

        let s = &self.buf[self.unmapped_head..self.unmapped_head + to_take];

        self.unmapped_head += to_take;

        Some(s)
    }
}

fn main() {
    let mut s = "abc%64%65fg".to_string();

    {
        let mut m = map_in_place(&mut s);

        while let Some(c) = m.pop() {
            match c {
                '%' => {
                    let num = m.pop_chars(2).expect("not enough chars");
                    let n = u8::from_str_radix(num, 16).expect("invalid hex");
                    m.push(n as char);
                }
                _ => m.push(c),
            }
        }
    }

    dbg!(&s);
}
