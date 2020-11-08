#[derive(Debug)]
pub struct MapInPlace<'a> {
    buf: &'a mut Vec<u8>,
    mapped_head: usize,
    unmapped_head: usize,
}

impl std::ops::Drop for MapInPlace<'_> {
    fn drop(&mut self) {
        self.buf.truncate(self.mapped_head);
    }
}

#[derive(Debug)]
pub struct NoCapacityError;

impl<'a> MapInPlace<'a> {
    /// Creates a new `MapInPlace`, used to do in-place string conversions without allocating a new
    /// buffer.
    ///
    /// This can only be done if the conversion does not increase the length of the string (So
    /// calling this on an empty string is useless).
    pub fn new(s: &'a mut String) -> Self {
        // I'm assuming that as_mut_vec has a similar requirement to str::as_bytes_mut
        // Namely, from now until the MapInPlace reference ends, the string is allowed to be invalid
        //
        // So as long as we fix up the string to be valid UTF-8 before the end of every function that
        // may have invalidated it, this is sound.
        //
        // Leaks are perfectly safe though! The only fixups we do in the Drop impl are to remove the
        // unmapped portion.
        unsafe {
            MapInPlace {
                buf: s.as_mut_vec(),
                mapped_head: 0,
                unmapped_head: 0,
            }
        }
    }

    /// Reads the mapped portion of the string
    pub fn mapped(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(&self.buf[0..self.mapped_head]) }
    }

    /// Reads the unmapped portion of the string
    pub fn unmapped(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(&self.buf[self.unmapped_head..]) }
    }

    fn fix_utf8(&mut self) {
        // This could be optimised, but for now this works.
        for ch in &mut self.buf[self.mapped_head..self.unmapped_head] {
            *ch = 0;
        }
    }

    /// Reads the string as a while. The contents of the section not included in either `mapped`
    /// or `unmapped` are unspecified, but the string as a whole is guaranteed to be valid UTF-8.
    pub fn all(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(&self.buf[..]) }
    }

    unsafe fn raw_push_bytes(&mut self, bytes: &[u8]) -> Result<(), NoCapacityError> {
        if self.buf.len() < self.mapped_head + bytes.len() {
            return Err(NoCapacityError);
        }
        self.buf[self.mapped_head..self.mapped_head + bytes.len()].copy_from_slice(bytes);

        Ok(())
    }

    /// Pushes a character onto the end of the mapped portion. Will return [`Err(NoCapacityError)`]
    /// if there is no room.
    pub fn push(&mut self, ch: char) -> Result<(), NoCapacityError> {
        let chlen = ch.len_utf8();

        if self.mapped_head + chlen > self.unmapped_head {
            return Err(NoCapacityError);
        }

        match chlen {
            1 => {
                *self.buf.get_mut(self.mapped_head).ok_or(NoCapacityError)? = ch as u8;
            }
            _ => {
                let mut tempbuf = [0_u8; 4_usize];
                let sbytes = ch.encode_utf8(&mut tempbuf).as_bytes();
                unsafe {
                    self.raw_push_bytes(&sbytes)?;
                }
            }
        }

        self.mapped_head += chlen;
        self.fix_utf8();

        Ok(())
    }

    pub fn push_str(&mut self, s: &str) -> Result<(), NoCapacityError> {
        if self.mapped_head + s.len() > self.unmapped_head {
            return Err(NoCapacityError);
        }

        unsafe {
            self.raw_push_bytes(&s.as_bytes())?;
        }

        self.mapped_head += s.len();
        self.fix_utf8();

        Ok(())
    }

    /// Pops a character from the start of the unmapped portion
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.unmapped().chars().next()?;

        let l = ch.len_utf8();

        self.unmapped_head += l;

        Some(ch)
    }

    /// Pops a character from the start of the unmapped portion
    ///
    /// If `n` is 0 then will always return [`None`]
    ///
    /// If this fails then `unmapped` will contain what can be popped, and no changes will have
    /// been made to `self`.
    pub fn pop_chars(&mut self, n: usize) -> Option<&str> {
        if n == 0 {
            return None;
        }

        let (idx, c) = self.unmapped().char_indices().nth(n - 1)?;

        let to_take = idx + c.len_utf8();

        let s = &self.buf[self.unmapped_head..self.unmapped_head + to_take];

        self.unmapped_head += to_take;

        unsafe { Some(std::str::from_utf8_unchecked(s)) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[derive(proptest_derive::Arbitrary, Debug)]
    enum TestOp {
        Pop,
        PopChars(usize),
        Push(char),
    }

    struct Model {
        unmapped: String,
        mapped: String,
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            max_global_rejects: 5000,
            ..Default::default()
        })]
        #[test]
        fn always_valid(mut start: String, ops: Vec<TestOp>) {
            let mut model = Model { unmapped: start.clone(), mapped: String::new()};

            let mut m = MapInPlace::new(&mut start);

            for o in ops {
                match o {
                    TestOp::Pop => {
                        let real = m.pop();

                        let model = if model.unmapped.len() == 0 {
                            None
                        } else {
                            Some(model.unmapped.remove(0))
                        };

                        assert_eq!(real, model);
                    },
                    TestOp::Push(c) => {
                        proptest::prop_assume!(m.push(c).is_ok());
                        model.mapped.push(c);
                    }
                    TestOp::PopChars(n) => {
                        let popped = m.pop_chars(n);

                        let model_str = {
                            if model.unmapped.len() < n || n == 0 {
                                None
                            } else {
                                let mut temp = String::new();
                                for _ in 0..n { temp.push(model.unmapped.remove(0)); }
                                Some(temp)
                            }
                        };

                        assert_eq!(popped, model_str.as_deref());
                    }
                }

                assert_eq!(std::str::from_utf8(m.all().as_bytes()).unwrap(), m.all(), "UTF-8 did not round trip");
                assert_eq!(m.unmapped(), model.unmapped, "unmapped did not match");
                assert_eq!(m.mapped(), model.mapped, "mapped did not match");
            }
        }
    }
}
