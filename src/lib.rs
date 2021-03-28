#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::nursery)]

#[derive(Debug)]
pub struct MapInPlace<'a> {
    buf: &'a mut [u8],
    mapped_head: usize,
    unmapped_head: usize,
}

#[derive(Debug)]
pub struct NoCapacityError;

impl<'a> MapInPlace<'a> {
    /// Creates a new `MapInPlace`, used to do in-place string conversions without allocating a new
    /// buffer.
    ///
    /// This can only be done if the conversion does not increase the length of the string (So
    /// calling this on an empty string is useless).
    pub fn new(s: &'a mut str) -> Self {
        // Safety:
        //
        // When this borrow ends (MapInPlace is dropped), the string must be valid UTF-8.
        // We also need to never expose invalid UTF-8 to the user.
        let buf = unsafe { s.as_bytes_mut() };

        MapInPlace {
            buf,
            mapped_head: 0,
            unmapped_head: 0,
        }
    }

    /// Returns the mapped portion of the string.
    #[must_use]
    pub fn mapped(&self) -> &str {
        &self.all()[0..self.mapped_head]
    }

    /// Consumes this [`MapInPlace`] and returns the mapped slice of the original string with the
    /// original lifetime.
    #[must_use]
    pub fn into_mapped(self) -> &'a mut str {
        let mapped_head = self.mapped_head;

        &mut self.into_all()[0..mapped_head]
    }

    /// Returns the not yet mapped portion of the string.
    #[must_use]
    pub fn unmapped(&self) -> &str {
        &self.all()[self.unmapped_head..]
    }

    /// Consumes this [`MapInPlace`] and returns the unmapped slice of the original string with the
    /// original lifetime.
    #[must_use]
    pub fn into_unmapped(self) -> &'a mut str {
        let unmapped_head = self.unmapped_head;

        &mut self.into_all()[unmapped_head..]
    }

    /// Reads the string as a whole. The contents of the section not included in either `mapped`
    /// or `unmapped` are unspecified, but the string as a whole is guaranteed to be valid UTF-8.
    #[must_use]
    pub fn all(&self) -> &str {
        // Safety: self.buf is always valid UTF-8 if the user has access to it, so this is safe.
        unsafe { std::str::from_utf8_unchecked(&self.buf[..]) }
    }

    /// Returns the original mapping given to [`MapInPlace::new`]. The contents of the section not
    /// included in either `mapped` or `unmapped` are unspecified, but the string as a whole is
    /// guaranteed to be valid UTF-8.
    #[must_use]
    pub fn into_all(self) -> &'a mut str {
        // Safety: self.buf is always valid UTF-8 if the user has access to it, so this is safe.
        unsafe { std::str::from_utf8_unchecked_mut(self.buf) }
    }

    /// Pushes a character onto the end of the mapped portion.
    ///
    /// # Errors
    ///
    /// * [`NoCapacityError`]: If there is not enough room to fit `ch` being pushed.
    pub fn push(&mut self, ch: char) -> Result<(), NoCapacityError> {
        let chlen = ch.len_utf8();

        if self.mapped_head + chlen > self.unmapped_head {
            return Err(NoCapacityError);
        }

        let mut tempbuf = [0_u8; 4_usize];

        let sbytes = ch.encode_utf8(&mut tempbuf);

        self.push_str(sbytes)?;

        Ok(())
    }

    /// Pushes a string onto the end of the mapped portion.
    ///
    /// # Errors
    ///
    /// * [`NoCapacityError`]: If there is not enough room to fit `s` being pushed.
    pub fn push_str(&mut self, s: &str) -> Result<(), NoCapacityError> {
        let bytes = s.as_bytes();

        if self.buf.len() < self.mapped_head + bytes.len() {
            return Err(NoCapacityError);
        }

        if self.unmapped_head < self.mapped_head + bytes.len() {
            return Err(NoCapacityError);
        }

        // Safety: self.buf must be valid UTF-8 once this ends.
        //
        // It consists of ..mapped_head, which is a `str` and we only push valid strs onto it
        // mapped_head..unmapped_head, which is zeroed out below, and thus valid UTF-8
        // unmapped_head.., which is a `str` and we only pop chars from it
        self.buf[self.mapped_head..self.mapped_head + bytes.len()].copy_from_slice(bytes);

        self.mapped_head += s.len();
        debug_assert!(self.mapped_head <= self.unmapped_head);

        self.buf[self.mapped_head..self.unmapped_head].fill(0);

        Ok(())
    }

    /// Pops a character from the start of the unmapped portion
    pub fn pop(&mut self) -> Option<char> {
        self.pop_chars(1)
            .map(|x| x.chars().next().expect("pop_chars did not pop a char"))
    }

    /// Pops `n` characters from the start of the unmapped portion
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

        // safety: who knows?
        unsafe { Some(std::str::from_utf8_unchecked(s)) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cannot_remove_from_end() {
        let mut initial = "㉉".to_string();
        let mut mapper = MapInPlace::new(&mut initial);
        mapper.pop_chars(3);
    }
}
