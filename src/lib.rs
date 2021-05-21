//! `in_place_string_map` is a library for doing string manipulation in place.
//!
//! Normally in Rust, if you wanted to handle escapes, for example, you'd need to either map to a
//! new String, causing allocations, or do `.remove` and `.insert` calls on a String, which
//! wouldn't cause reallocations if you never grow the String, but *would* cause slowdowns on large
//! strings due to the need to backshift elements on every item.
//!
//! Here, you can just do
//!
//! ```rust
//! use in_place_string_map::MapInPlace;
//!
//! fn decode_percent(s: &mut str) -> &mut str {
//!     let mut m = MapInPlace::new(s);
//!
//!     while let Some(c) = m.pop() {
//!         match c {
//!             '%' => {
//!                 let num = m.pop_chars(2).expect("not enough chars");
//!                 let n = u8::from_str_radix(num, 16).expect("invalid hex");
//!                 m.push(n as char).expect("no more capacity");
//!             }
//!             _ => {
//!                 m.push(c).expect("no more capacity");
//!             }
//!         }
//!     }
//!
//!     m.into_mapped()
//! }
//!
//! let mut input = String::from("%54r%61ns %52igh%74%73%21");
//!
//! assert_eq!(decode_percent(&mut input), "Trans Rights!");
//! ```
//!
//! ## Safety
//!
//! This library takes care to ensure that the input string is always left in a valid state.
//!
//! Since [`core::mem::forget`] is safe, no code can soundly rely on users to call destructors. The
//! contents of the original borrowed string after any operation is left unspecified generally, but
//! it is guaranteed to always be valid UTF-8.

// https://twitter.com/reduct_rs/status/1387153973010829315
#![cfg_attr(all(not(test)), no_std)]
#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::nursery)]
#![warn(clippy::cargo)]
#![warn(missing_docs)]

/// Safety: Identical to [`core::str::from_utf8_unchecked`], only has a debug assertion that it is
/// indeed valid UTF-8.
unsafe fn from_utf8_unchecked(input: &[u8]) -> &str {
    debug_assert!(
        core::str::from_utf8(input).is_ok(),
        "{:?} was invalid UTF-8",
        input
    );

    core::str::from_utf8_unchecked(input)
}

/// Safety: Identical to [`core::str::from_utf8_unchecked_mut`], only has a debug assertion that it is
/// indeed valid UTF-8.
unsafe fn from_utf8_unchecked_mut(input: &mut [u8]) -> &mut str {
    debug_assert!(
        core::str::from_utf8(input).is_ok(),
        "{:?} was invalid UTF-8",
        input
    );

    core::str::from_utf8_unchecked_mut(input)
}

#[derive(Debug)]
/// A mutable reference to a [`str`] that allows for in-place pushes and pops while maintaining
/// valid UTF-8 at all times.
///
/// Semantically, this creates 2 buffers, a "mapped" buffer, and an "unmapped" buffer.
///
/// The mapped buffer starts off empty, and the unmapped buffer starts off with the full contents
/// of the `&mut str` given in [`MapInPlace::new`].
///
/// The mapped buffer can be pushed to, and this will append to the end of it. The unmapped buffer
/// can be popped from, and this will pop from the start of it.
///
/// The size of the mapped buffer, plus the size of the unmapped buffer, can never be bigger than
/// the original string size, and you will get errors when you go to push if this is the case.
///
/// However, it's free to be smaller, in which case there will be some area in the middle with
/// unspecified contents. It will still be valid UTF-8 though, to ensure safety.
pub struct MapInPlace<'a> {
    /// Invariants:
    ///
    /// * This must always be valid UTF-8 when the [`MapInPlace`] is exposed to code
    /// outside this crate.
    buf: &'a mut [u8],

    /// Invariants:
    ///
    /// * `0..mapped_head` must always be in bounds for [`MapInPlace.buf`]
    /// * `0..mapped_head` must always be valid UTF-8 (when exposed to code outside this crate)
    mapped_head: usize,

    /// Invariants:
    ///
    /// * `unmapped_head` must be in bounds
    /// * `unmapped_head..` always in bounds for [`MapInPlace.buf`]
    unmapped_head: usize,
}

/// Checks that `byte` is the first byte in a UTF-8 code point
/// sequence
///
/// Based of std library [`str::is_char_boundary`]
#[inline]
// we intentionally wrap here
#[allow(clippy::cast_possible_wrap)]
const fn is_char_start(byte: u8) -> bool {
    // This is bit magic equivalent to: b < 128 || b >= 192
    (byte as i8) >= -0x40
}

/// An error indicating that there was no capacity remaining when a push was attempted.
///
/// You should [`MapInPlace::pop`] more characters in order to make room for a push.
///
/// Keep in mind that not every UTF-8 character is the same size, so you may get this error even if
/// you always have more pops than pushes, if you are pushing larger characters.
///
/// # Examples
///
/// ```rust
/// use in_place_string_map::{MapInPlace, NoCapacityError};
///
/// let mut string = String::from("$");
/// let mut map = MapInPlace::new(&mut string);
///
/// map.pop();
///
/// let error: NoCapacityError = map.push('£').unwrap_err();
/// ```
#[derive(Debug)]
pub struct NoCapacityError(());

// When zeroing sections of the string to ensure valid UTF-8, anything smaller than this will just
// be zeroed with a .fill(), rather than trying to stop early.
//
// Anything larger will try to stop as early as it can and still ensure valid UTF-8
const PARTIAL_ZERO_SIZE: usize = 32;

impl<'a> MapInPlace<'a> {
    /// Creates a new `MapInPlace`, used to do in-place string conversions without allocating a new
    /// buffer.
    ///
    /// ```rust
    /// let mut string = String::from("Hello, World!");
    /// let mut map = in_place_string_map::MapInPlace::new(&mut string);
    /// ```
    pub fn new(s: &'a mut str) -> Self {
        // Safety:
        //
        // When this borrow ends (MapInPlace is dropped/forgotten), the string must be valid UTF-8.
        // We also need to never expose invalid UTF-8 to the user.
        let buf = unsafe { s.as_bytes_mut() };

        MapInPlace {
            buf,
            mapped_head: 0,
            unmapped_head: 0,
        }
    }

    /// Returns the mapped portion of the string.
    ///
    /// ```rust
    /// let mut string = String::from("Hello, World!");
    /// let mut map = in_place_string_map::MapInPlace::new(&mut string);
    ///
    /// assert_eq!(map.mapped(), "");
    ///
    /// map.pop_chars(6);
    ///
    /// map.push_str("Yellow");
    ///
    /// assert_eq!(map.mapped(), "Yellow");
    /// ```
    #[must_use]
    pub fn mapped(&self) -> &str {
        debug_assert!(self.buf.get(0..self.mapped_head).is_some());

        // Safety: self.mapped_head has the invariant that it is always in bounds of `buf`.
        let bytes = unsafe { self.buf.get_unchecked(0..self.mapped_head) };

        unsafe { from_utf8_unchecked(bytes) }
    }

    /// Consumes this [`MapInPlace`] and returns the mapped slice of the original string with the
    /// original lifetime.
    ///
    /// This is useful for when you want the lifetime of the returned string to outlive the
    /// instance of [`MapInPlace`].
    ///
    /// ```rust
    /// fn push_yellow(s: &mut str) -> &mut str {
    ///     let mut map = in_place_string_map::MapInPlace::new(s);
    ///     map.pop_chars(6);
    ///     map.push_str("Yellow");
    ///     map.into_mapped()
    /// }
    ///
    /// let mut string = String::from("Hello, World!");
    /// let result = push_yellow(&mut string);
    /// assert_eq!(result, "Yellow");
    /// ```
    ///
    /// You cannot simply use [`MapInPlace::mapped`] because that will return a reference that
    /// can't outlive the original [`MapInPlace`]
    ///
    /// ```compile_fail
    /// fn push_yellow(s: &mut str) -> &str {
    ///     let mut map = in_place_string_map::MapInPlace::new(s);
    ///     map.pop_chars(6);
    ///     map.push_str("Yellow");
    ///
    ///     // cannot return value referencing local variable `map`
    ///     map.mapped()
    /// }
    ///
    /// let mut string = String::from("Hello, World!");
    /// let result = push_yellow(&mut string);
    /// assert_eq!(result, "Yellow");
    /// ```
    #[must_use]
    pub fn into_mapped(self) -> &'a mut str {
        let mapped_head = self.mapped_head;

        &mut self.into_all()[0..mapped_head]
    }

    /// Returns the not yet mapped portion of the string.
    ///
    /// ```rust
    /// let mut string = String::from("Hello, World!");
    /// let mut map = in_place_string_map::MapInPlace::new(&mut string);
    ///
    /// assert_eq!(map.unmapped(), "Hello, World!");
    ///
    /// map.pop_chars(5);
    ///
    /// assert_eq!(map.unmapped(), ", World!");
    /// ```
    #[must_use]
    pub fn unmapped(&self) -> &str {
        &self.all()[self.unmapped_head..]
    }

    /// Consumes this [`MapInPlace`] and returns the unmapped slice of the original string with the
    /// original lifetime.
    ///
    /// This is useful for when you want the lifetime of the returned string to outlive the
    /// instance of [`MapInPlace`].
    ///
    /// ```rust
    /// fn pop_five(s: &mut str) -> &mut str {
    ///     let mut map = in_place_string_map::MapInPlace::new(s);
    ///     map.pop_chars(5);
    ///     map.into_unmapped()
    /// }
    ///
    /// let mut string = String::from("Hello, World!");
    /// let result = pop_five(&mut string);
    /// assert_eq!(result, ", World!");
    /// ```
    ///
    /// You cannot simply use [`MapInPlace::mapped`] because that will return a reference that
    /// can't outlive the original [`MapInPlace`]
    ///
    /// ```compile_fail
    /// fn pop_five(s: &mut str) -> &str {
    ///     let mut map = in_place_string_map::MapInPlace::new(s);
    ///     map.pop_chars(5);
    ///
    ///     // cannot return value referencing local variable `map`
    ///     map.unmapped()
    /// }
    ///
    /// let mut string = String::from("Hello, World!");
    /// let result = pop_five(&mut string);
    /// assert_eq!(result, ", World!");
    /// ```
    #[must_use]
    pub fn into_unmapped(self) -> &'a mut str {
        let unmapped_head = self.unmapped_head;

        &mut self.into_all()[unmapped_head..]
    }

    #[must_use]
    fn all(&self) -> &str {
        // Safety: self.buf is always valid UTF-8 if the user has access to it, so this is safe.
        unsafe { from_utf8_unchecked(&self.buf[..]) }
    }

    #[must_use]
    fn into_all(self) -> &'a mut str {
        // Safety: self.buf is always valid UTF-8 if the user has access to it, so this is safe.
        unsafe { from_utf8_unchecked_mut(self.buf) }
    }

    /// Pushes a character onto the end of the mapped portion.
    ///
    /// ```rust
    /// let mut string = String::from("Hello!");
    /// let mut map = in_place_string_map::MapInPlace::new(&mut string);
    /// map.pop_chars(6);
    ///
    /// assert_eq!(map.mapped(), "");
    /// map.push('£').unwrap();
    /// map.push('1').unwrap();
    /// map.push('.').unwrap();
    /// map.push('2').unwrap();
    /// map.push('5').unwrap();
    ///
    /// assert_eq!(map.mapped(), "£1.25");
    ///
    /// map.push('5').unwrap_err();
    ///
    /// assert_eq!(map.mapped(), "£1.25");
    /// ```
    ///
    /// # Errors
    ///
    /// * [`NoCapacityError`]: If there is not enough room to fit `ch` being pushed.
    pub fn push(&mut self, ch: char) -> Result<(), NoCapacityError> {
        let mut tempbuf = [0_u8; 4_usize];

        let sbytes = ch.encode_utf8(&mut tempbuf);

        self.push_str(sbytes)?;

        Ok(())
    }

    /// Pushes a string onto the end of the mapped portion. If the string is too long, an error is
    /// returned, and no changes will be made to the input.
    ///
    /// ```rust
    /// let mut string = String::from("Hello!");
    /// let mut map = in_place_string_map::MapInPlace::new(&mut string);
    /// map.pop_chars(6);
    ///
    /// assert_eq!(map.mapped(), "");
    ///
    /// map.push_str("This string is *far* too long!").unwrap_err();
    ///
    /// assert_eq!(map.mapped(), "");
    ///
    /// map.push_str("Short").unwrap();
    ///
    /// assert_eq!(map.mapped(), "Short");
    ///
    /// map.push_str(".").unwrap();
    ///
    /// assert_eq!(map.mapped(), "Short.");
    /// ```
    ///
    /// # Errors
    ///
    /// * [`NoCapacityError`]: If there is not enough room to fit `s` being pushed.
    pub fn push_str(&mut self, s: &str) -> Result<(), NoCapacityError> {
        let bytes = s.as_bytes();

        if self.buf.len() < self.mapped_head + bytes.len() {
            return Err(NoCapacityError(()));
        }

        if self.unmapped_head < self.mapped_head + bytes.len() {
            return Err(NoCapacityError(()));
        }

        // Safety: self.buf must be valid UTF-8 once this ends.
        //
        // It consists of:
        // ..mapped_head, which is a `str` and we only push valid strs onto it
        // mapped_head..unmapped_head, which consists of the previous contents of the str
        //   where an unspecified amount is zeroed
        // unmapped_head.., which is a `str` and we only pop chars from it
        self.buf[self.mapped_head..self.mapped_head + bytes.len()].copy_from_slice(bytes);

        self.mapped_head += bytes.len();
        debug_assert!(self.mapped_head <= self.unmapped_head);

        let area_to_zero = &mut self.buf[self.mapped_head..self.unmapped_head];

        if area_to_zero.len() > PARTIAL_ZERO_SIZE {
            for byte in area_to_zero {
                if is_char_start(*byte) {
                    break;
                }
                *byte = 0;
            }
        } else {
            area_to_zero.fill(0);
        }

        Ok(())
    }

    /// Pops a character from the start of the unmapped portion
    ///
    /// Will return [`None`] if there are no more characters left to pop.
    ///
    /// ```rust
    /// let mut string = String::from("Hi!");
    /// let mut map = in_place_string_map::MapInPlace::new(&mut string);
    ///
    /// assert_eq!(map.pop(), Some('H'));
    /// assert_eq!(map.unmapped(), "i!");
    ///
    /// assert_eq!(map.pop(), Some('i'));
    /// assert_eq!(map.unmapped(), "!");
    ///
    /// assert_eq!(map.pop(), Some('!'));
    /// assert_eq!(map.unmapped(), "");
    ///
    /// assert_eq!(map.pop(), None);
    /// assert_eq!(map.unmapped(), "");
    /// ```
    pub fn pop(&mut self) -> Option<char> {
        self.pop_chars(1)
            .map(|x| x.chars().next().expect("pop_chars did not pop a char"))
    }

    /// Pops `n` characters from the start of the unmapped portion.
    ///
    /// Note how this pops in terms of *characters*, not bytes.
    ///
    /// If `n` is 0 then will always return [`None`]
    ///
    /// If this fails because there are not enough characters then will return [`None`], and no
    /// changes will have been made to `self`.
    ///
    /// ```rust
    /// let mut string = String::from("A £3.00 sandwich");
    /// let mut map = in_place_string_map::MapInPlace::new(&mut string);
    ///
    /// assert_eq!(map.pop_chars(0), None);
    /// assert_eq!(map.pop_chars(2), Some("A "));
    /// assert_eq!(map.pop_chars(5), Some("£3.00"));
    ///
    /// // Nothing is done if you try to pop too many characters
    /// assert_eq!(map.pop_chars(10), None);
    ///
    /// assert_eq!(map.pop_chars(9), Some(" sandwich"));
    /// ```
    pub fn pop_chars(&mut self, n: usize) -> Option<&str> {
        if n == 0 {
            return None;
        }

        let (idx, c) = self.unmapped().char_indices().nth(n - 1)?;

        let to_take = idx + c.len_utf8();

        let s = &self.buf[self.unmapped_head..self.unmapped_head + to_take];

        self.unmapped_head += to_take;

        // Safety of from_utf8_unchecked:
        //
        // We slice the buffer starting at the original value for self.unmapped_head, which must be
        // on a char boundary, this is an invariant of the type for safety (otherwise,
        // self.unmapped() would create invalid UTF-8).
        //
        // self.unmapped_head is incremented by to_take, which also leaves it on a char boundary,
        // because `idx` is on a char boundary when looked at relative to self.unmapped_head (since
        // we got it from char_indices on self.unmapped())
        //
        // We add c.len_utf8() on top, which makes to_take on a char boundary relative to
        // self.unmapped_head.
        //
        // Therefore, `s` is always valid UTF-8.

        // We also need to keep the invariant that self.unmapped_head is always on a char boundary.
        // But we already know it must be, since we're adding `to_take` to it, which the argument
        // above proves is on a char boundary.
        unsafe { Some(from_utf8_unchecked(s)) }
    }
}

// Source: https://github.com/rust-lang/cargo/issues/383#issuecomment-720873790
#[cfg(doctest)]
mod test_readme {
    macro_rules! external_doc_test {
        ($x:expr) => {
            #[doc = $x]
            extern "C" {}
        };
    }

    external_doc_test!(include_str!("../README.md"));
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
