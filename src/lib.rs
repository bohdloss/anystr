#![cfg_attr(doc_cfg, feature(doc_cfg))]
#![cfg_attr(feature = "unstable", feature(error_in_core))]
#![cfg_attr(not(feature = "std"), no_std)]
#[cfg(feature = "alloc")]
extern crate alloc;
extern crate core;

macro_rules! impl_error {
    ($name:ident) => {
	    #[cfg(feature = "unstable")]
		impl core::error::Error for $name {}

		#[cfg(all(not(feature = "unstable"), feature = "std"))]
		impl std::error::Error for $name {}
    };
}
use core::mem::size_of;
use core::char;
pub(crate) use impl_error;

#[cfg(feature = "alloc")]
mod use_ {
	pub use alloc::string::String;
	pub use ascii::AsciiString;
	pub use widestring::{Utf16String, Utf32String};
}

use ascii::{AsAsciiStrError, AsciiStr, ToAsciiCharError};
use parse_display::Display;
use widestring::{Utf16Str, Utf32Str};
#[cfg(feature = "alloc")]
use use_::*;

/// A generic string encoding enum, used as a preference for many string initialization operations.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Encoding {
	Ascii,
	Utf8,
	Utf16,
	Utf32,
}

impl Encoding {
	/// Returns true only if `self` is ASCII
	#[inline]
	pub const fn is_ascii(&self) -> bool {
		match self {
			Encoding::Ascii => true,
			_ => false,
		}
	}

	/// Returns true only if `self` is ASCII
	#[inline]
	pub const fn is_utf8(&self) -> bool {
		match self {
			Encoding::Utf8 => true,
			_ => false,
		}
	}

	/// Returns true only if `self` is ASCII
	#[inline]
	pub const fn is_utf16(&self) -> bool {
		match self {
			Encoding::Utf16 => true,
			_ => false,
		}
	}

	/// Returns true only if `self` is ASCII
	#[inline]
	pub const fn is_utf32(&self) -> bool {
		match self {
			Encoding::Utf32 => true,
			_ => false,
		}
	}

	/// Returns the number of bytes per element this encoding uses.
	#[inline]
	pub const fn bytes(&self) -> usize {
		match self {
			Encoding::Ascii => size_of::<u8>(),
			Encoding::Utf8 => size_of::<u8>(),
			Encoding::Utf16 => size_of::<u16>(),
			Encoding::Utf32 => size_of::<u32>(),
		}
	}
}

#[derive(Debug, Display)]
pub enum AsciiError {
	#[display("AsAsciiStrError: {0}")]
	AsAsciiStrError(AsAsciiStrError),
	#[display("ToAsciiCharError: {0}")]
	ToAsciiCharError(ToAsciiCharError),
}

impl From<AsAsciiStrError> for AsciiError {
	fn from(value: AsAsciiStrError) -> Self {
		Self::AsAsciiStrError(value)
	}
}

impl From<ToAsciiCharError> for AsciiError {
	fn from(value: ToAsciiCharError) -> Self {
		Self::ToAsciiCharError(value)
	}
}

impl_error!(AsciiError);

#[derive(Debug, Display)]
pub enum ConversionError {
	#[display("The string couldn't be converted to ASCII: {0}")]
	InvalidAscii(AsciiError),
}

impl From<AsciiError> for ConversionError {
	fn from(value: AsciiError) -> Self {
		Self::InvalidAscii(value)
	}
}

impl_error!(ConversionError);

/// An enum that encapsulates an owned string type and encoding while "re-exporting"
/// many of the methods found on a `String`.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum AnyString {
	Ascii(AsciiString),
	Utf8(String),
	Utf16(Utf16String),
	Utf32(Utf32String)
}

#[cfg(feature = "alloc")]
impl AnyString {
	/// Creates a new empty `AnyString` with the given [`Encoding`].
	///
	/// Given that the `AnyString` is empty, this will not allocate any initial
	/// buffer. While that means that this initial operation is very
	/// inexpensive, it may cause excessive allocation later when you add
	/// data. If you have an idea of how much data the `String` will hold,
	/// consider the [`with_capacity`] method to prevent excessive
	/// re-allocation.
	///
	/// [`with_capacity`]: AnyString::with_capacity
	///
	/// # Examples
	///
	/// ```
	/// use anystr::{AnyString, Encoding};
	/// let s = AnyString::new(Encoding::Utf8);
	/// ```
	#[inline]
	pub const fn new(encoding: Encoding) -> Self {
		match encoding {
			Encoding::Ascii => Self::Ascii(AsciiString::new()),
			Encoding::Utf8 => Self::Utf8(String::new()),
			Encoding::Utf16 => Self::Utf16(Utf16String::new()),
			Encoding::Utf32 => Self::Utf32(Utf32String::new()),
		}
	}

	/// Creates a new empty `AnyString` with at least the specified capacity
	/// and the given [`Encoding`].
	///
	/// `AnyString`s have an internal buffer to hold their data. The capacity is
	/// the length of that buffer, and can be queried with the [`capacity`]
	/// method. This method creates an empty `String`, but one with an initial
	/// buffer that can hold at least `capacity` bytes. This is useful when you
	/// may be appending a bunch of data to the `String`, reducing the number of
	/// reallocations it needs to do.
	///
	/// [`capacity`]: AnyString::capacity
	///
	/// If the given capacity is `0`, no allocation will occur, and this method
	/// is identical to the [`new`] method.
	///
	/// [`new`]: AnyString::new
	///
	/// # Examples
	///
	/// ```
	/// use anystr::{AnyString, Encoding};
	/// let mut s = AnyString::with_capacity(10, Encoding::Utf8);
	///
	/// // The String contains no chars, even though it has capacity for more
	/// assert_eq!(s.len(), 0);
	///
	/// // These are all done without reallocating...
	/// let cap = s.capacity();
	/// for _ in 0..10 {
	///     s.push('a').unwrap();
	/// }
	///
	/// assert_eq!(s.capacity(), cap);
	///
	/// // ...but this may make the string reallocate
	/// s.push('a').unwrap();
	/// ```
	#[inline]
	pub fn with_capacity(capacity: usize, encoding: Encoding) -> Self {
		let capacity = capacity / encoding.bytes();
		match encoding {
			Encoding::Ascii => Self::Ascii(AsciiString::with_capacity(capacity)),
			Encoding::Utf8 => Self::Utf8(String::with_capacity(capacity)),
			Encoding::Utf16 => Self::Utf16(Utf16String::with_capacity(capacity)),
			Encoding::Utf32 => Self::Utf32(Utf32String::with_capacity(capacity)),
		}
	}

	/// Wraps the given string into an allocated string type that uses the given `encoding`.
	/// This function will fail if unsupported characters for the specific encoding are found.
	#[inline]
	pub fn from_str<T: AsRef<str> + ?Sized>(s: &T, encoding: Encoding) -> Result<AnyString, ConversionError> {
		match encoding {
			Encoding::Ascii => {
				use core::str::FromStr;
				let ascii = AsciiString::from_str(s.as_ref()).map_err(AsciiError::from)?;
				Ok(AnyString::Ascii(ascii))
			}
			Encoding::Utf8 => {
				let utf8 = String::from(s.as_ref());
				Ok(AnyString::Utf8(utf8))
			}
			Encoding::Utf16 => {
				let utf16 = Utf16String::from(s.as_ref());
				Ok(AnyString::Utf16(utf16))
			}
			Encoding::Utf32 => {
				let utf32 = Utf32String::from(s.as_ref());
				Ok(AnyString::Utf32(utf32))
			}
		}
	}

	/// Returns this `AnyString`'s capacity, in bytes.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::{AnyString, Encoding};
	/// let s = AnyString::with_capacity(10, Encoding::Utf8);
	///
	/// assert!(s.capacity() >= 10);
	/// ```
	#[must_use]
	#[inline]
	pub fn capacity(&self) -> usize {
		let capacity = match self {
			AnyString::Ascii(x) => x.capacity(),
			AnyString::Utf8(x) => x.capacity(),
			AnyString::Utf16(x) => x.capacity(),
			AnyString::Utf32(x) => x.capacity(),
		};
		self.get_encoding().bytes() * capacity
	}

	/// Returns the underlying [string encoding][`Encoding`].
	#[inline]
	pub fn get_encoding(&self) -> Encoding {
		match self {
			AnyString::Ascii(_) => Encoding::Ascii,
			AnyString::Utf8(_) => Encoding::Utf8,
			AnyString::Utf16(_) => Encoding::Utf16,
			AnyString::Utf32(_) => Encoding::Utf32,
		}
	}

	/// Reserves capacity for at least `additional` bytes more than the
	/// current length. The allocator may reserve more space to speculatively
	/// avoid frequent allocations. After calling `reserve`,
	/// capacity will be greater than or equal to `self.len() + additional`.
	/// Does nothing if capacity is already sufficient.
	///
	/// # Panics
	///
	/// Panics if the new capacity overflows [`usize`].
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```
	/// use anystr::{AnyString, Encoding};
	/// let mut s = AnyString::new(Encoding::Utf8);
	///
	/// s.reserve(10);
	///
	/// assert!(s.capacity() >= 10);
	/// ```
	///
	/// This might not actually increase the capacity:
	///
	/// ```
	/// use anystr::{AnyString, Encoding};
	/// let mut s = AnyString::with_capacity(10, Encoding::Utf8);
	/// s.push('a').unwrap();
	/// s.push('b').unwrap();
	///
	/// // s now has a length of 2 and a capacity of at least 10
	/// let capacity = s.capacity();
	/// assert_eq!(2, s.len());
	/// assert!(capacity >= 10);
	///
	/// // Since we already have at least an extra 8 capacity, calling this...
	/// s.reserve(8);
	///
	/// // ... doesn't actually increase.
	/// assert_eq!(capacity, s.capacity());
	/// ```
	#[inline]
	pub fn reserve(&mut self, additional: usize) {
		let additional = additional / self.get_encoding().bytes();
		match self {
			AnyString::Ascii(x) => x.reserve(additional),
			AnyString::Utf8(x) => x.reserve(additional),
			AnyString::Utf16(x) => x.reserve(additional),
			AnyString::Utf32(x) => x.reserve(additional),
		}
	}

	/// Reserves the minimum capacity for at least `additional` bytes more than
	/// the current length. Unlike [`reserve`], this will not
	/// deliberately over-allocate to speculatively avoid frequent allocations.
	/// After calling `reserve_exact`, capacity will be greater than or equal to
	/// `self.len() + additional`. Does nothing if the capacity is already
	/// sufficient.
	///
	/// [`reserve`]: AnyString::reserve
	///
	/// # Panics
	///
	/// Panics if the new capacity overflows [`usize`].
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```
	/// use anystr::{AnyString, Encoding};
	/// let mut s = AnyString::new(Encoding::Utf8);
	///
	/// s.reserve_exact(10);
	///
	/// assert!(s.capacity() >= 10);
	/// ```
	///
	/// This might not actually increase the capacity:
	///
	/// ```
	/// use anystr::{AnyString, Encoding};
	/// let mut s = AnyString::with_capacity(10, Encoding::Utf8);
	/// s.push('a').unwrap();
	/// s.push('b').unwrap();
	///
	/// // s now has a length of 2 and a capacity of at least 10
	/// let capacity = s.capacity();
	/// assert_eq!(2, s.len());
	/// assert!(capacity >= 10);
	///
	/// // Since we already have at least an extra 8 capacity, calling this...
	/// s.reserve_exact(8);
	///
	/// // ... doesn't actually increase.
	/// assert_eq!(capacity, s.capacity());
	/// ```
	#[inline]
	pub fn reserve_exact(&mut self, additional: usize) {
		let additional = additional / self.get_encoding().bytes();
		match self {
			AnyString::Ascii(x) => x.reserve_exact(additional),
			AnyString::Utf8(x) => x.reserve_exact(additional),
			AnyString::Utf16(x) => x.reserve_exact(additional),
			AnyString::Utf32(x) => x.reserve_exact(additional),
		}
	}

	/// Shrinks the capacity of this `AnyString` to match its length.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyString;
	/// let mut s = AnyString::from("foo");
	///
	/// s.reserve(100);
	/// assert!(s.capacity() >= 100);
	///
	/// s.shrink_to_fit();
	/// assert_eq!(3, s.capacity());
	/// ```
	#[inline]
	pub fn shrink_to_fit(&mut self) {
		match self {
			AnyString::Ascii(x) => x.shrink_to_fit(),
			AnyString::Utf8(x) => x.shrink_to_fit(),
			AnyString::Utf16(x) => x.shrink_to_fit(),
			AnyString::Utf32(x) => x.shrink_to_fit(),
		}
	}

	/// Shrinks the capacity of this `String` with a lower bound.
	///
	/// The capacity will remain at least as large as both the length
	/// and the supplied value.
	///
	/// If the current capacity is less than the lower limit, this is a no-op.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyString;
	/// let mut s = AnyString::from("foo");
	///
	/// s.reserve(100);
	/// assert!(s.capacity() >= 100);
	///
	/// s.shrink_to(10);
	/// assert!(s.capacity() >= 10);
	/// s.shrink_to(0);
	/// assert!(s.capacity() >= 3);
	/// ```
	#[inline]
	pub fn shrink_to(&mut self, min_capacity: usize) {
		let min_capacity = min_capacity / self.get_encoding().bytes();
		match self {
			AnyString::Ascii(x) => {
				if min_capacity <= x.len() {
					return x.shrink_to_fit();
				} else if min_capacity == x.capacity() {
					return;
				} else if min_capacity < x.capacity() {
					let mut ascii = AsciiString::new();
					ascii.reserve_exact(min_capacity);
					ascii.push_str(&x);
					*x = ascii;
				} /* else if min_capacity > x.capacity() */
			},
			AnyString::Utf8(x) => x.shrink_to(min_capacity),
			AnyString::Utf16(x) => x.shrink_to(min_capacity),
			AnyString::Utf32(x) => x.shrink_to(min_capacity),
		}
	}

	/// Returns the length of this `AnyString`, in bytes, not [`char`]s or
	/// graphemes. In other words, it might not be what a human considers the
	/// length of the string.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyString;
	/// let a = AnyString::from("foo");
	/// assert_eq!(a.len(), 3);
	///
	/// let fancy_f = AnyString::from("ƒoo");
	/// assert_eq!(fancy_f.len(), 4);
	/// assert_eq!(fancy_f.chars().count(), 3);
	/// ```
	#[inline]
	#[must_use]
	pub fn len(&self) -> usize {
		let len = match self {
			AnyString::Ascii(x) => x.len(),
			AnyString::Utf8(x) => x.len(),
			AnyString::Utf16(x) => x.len(),
			AnyString::Utf32(x) => x.len(),
		};
		self.get_encoding().bytes() * len
	}

	/// Returns `true` if this `String` has a length of zero, and `false` otherwise.
	///
	/// # Examples
	///
	/// ```
	/// let mut v = String::new();
	/// assert!(v.is_empty());
	///
	/// v.push('a');
	/// assert!(!v.is_empty());
	/// ```
	#[inline]
	#[must_use]
	pub fn is_empty(&self) -> bool {
		match self {
			AnyString::Ascii(x) => x.is_empty(),
			AnyString::Utf8(x) => x.is_empty(),
			AnyString::Utf16(x) => x.is_empty(),
			AnyString::Utf32(x) => x.is_empty(),
		}
	}

	/// Truncates this `AnyString`, removing all contents.
	///
	/// While this means the `AnyString` will have a length of zero, it does not
	/// touch its capacity.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyString;
	/// let mut s = AnyString::from("foo");
	///
	/// s.clear();
	///
	/// assert!(s.is_empty());
	/// assert_eq!(0, s.len());
	/// assert_eq!(3, s.capacity());
	/// ```
	#[inline]
	pub fn clear(&mut self) {
		match self {
			AnyString::Ascii(x) => x.clear(),
			AnyString::Utf8(x) => x.clear(),
			AnyString::Utf16(x) => x.clear(),
			AnyString::Utf32(x) => x.clear(),
		}
	}

	/// Appends the given [`char`] to the end of this `AnyString`.
	///
	/// An error is returned if the string contains characters not
	/// supported by the encoding.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyString;
	/// let mut s = AnyString::from("abc");
	///
	/// s.push('1').unwrap();
	/// s.push('2').unwrap();
	/// s.push('3').unwrap();
	///
	/// assert_eq!(s, "abc123");
	/// ```
	#[inline]
	pub fn push(&mut self, ch: char) -> Result<(), ConversionError> {
		use ascii::ToAsciiChar;
		match self {
			AnyString::Ascii(x) => Ok(x.push(ch.to_ascii_char().map_err(AsciiError::from)?)),
			AnyString::Utf8(x) => Ok(x.push(ch)),
			AnyString::Utf16(x) => Ok(x.push(ch)),
			AnyString::Utf32(x) => Ok(x.push(ch)),
		}
	}

	/// Appends a given string slice onto the end of this `AnyString`.
	///
	/// An error is returned if the string contains characters not
	/// supported by the encoding.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyString;
	/// let mut s = AnyString::from("foo");
	///
	/// s.push_str("bar").unwrap();
	///
	/// assert_eq!(s, "foobar");
	/// ```
	#[inline]
	pub fn push_str<T: AsRef<str> + ?Sized>(&mut self, string: &T) -> Result<(), ConversionError> {
		match self {
			AnyString::Ascii(x) => {
				let ascii_str = AsciiStr::from_ascii(string.as_ref().as_bytes()).map_err(AsciiError::from)?;
				Ok(x.push_str(ascii_str))
			},
			AnyString::Utf8(x) => Ok(x.push_str(string.as_ref())),
			AnyString::Utf16(x) => Ok(x.push_str(string.as_ref())),
			AnyString::Utf32(x) => Ok(x.push_str(string.as_ref())),
		}
	}

	/// Shortens this `AnyString` to the specified length.
	///
	/// If `new_len` is greater than the string's current length, this has no
	/// effect.
	///
	/// Note that this method has no effect on the allocated capacity
	/// of the string
	///
	/// # Panics
	///
	/// Panics if `new_len` does not lie on a [`char`] boundary.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyString;
	/// let mut s = AnyString::from("hello");
	///
	/// s.truncate(2);
	///
	/// assert_eq!(s, "he");
	/// ```
	#[inline]
	pub fn truncate(&mut self, new_len: usize) {
		let new_len = new_len / self.get_encoding().bytes();
		if new_len >= self.len() {
			return;
		}
		match self {
			AnyString::Ascii(x) => x.truncate(new_len),
			AnyString::Utf8(x) => x.truncate(new_len),
			AnyString::Utf16(x) => x.truncate(new_len),
			AnyString::Utf32(x) => x.truncate(new_len),
		}
	}

	/// Removes the last character from the string buffer and returns it.
	///
	/// Returns [`None`] if this `String` is empty.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyString;
	/// let mut s = AnyString::from("abč");
	///
	/// assert_eq!(s.pop(), Some('č'));
	/// assert_eq!(s.pop(), Some('b'));
	/// assert_eq!(s.pop(), Some('a'));
	///
	/// assert_eq!(s.pop(), None);
	/// ```
	#[inline]
	pub fn pop(&mut self) -> Option<char> {
		match self {
			AnyString::Ascii(x) => x.pop().map(|ch| ch.as_char()),
			AnyString::Utf8(x) => x.pop(),
			AnyString::Utf16(x) => x.pop(),
			AnyString::Utf32(x) => x.pop(),
		}
	}

	/// Removes a [`char`] from this `AnyString` at a byte position and returns it.
	///
	/// This is an *O*(*n*) operation, as it requires copying every element in the
	/// buffer.
	///
	/// # Panics
	///
	/// Panics if `idx` is larger than or equal to the `AnyString`'s length,
	/// or if it does not lie on a [`char`] boundary.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyString;
	/// let mut s = AnyString::from("abç");
	///
	/// assert_eq!(s.remove(0), 'a');
	/// assert_eq!(s.remove(1), 'ç');
	/// assert_eq!(s.remove(0), 'b');
	/// ```
	#[inline]
	pub fn remove(&mut self, idx: usize) -> char {
		let idx = idx / self.get_encoding().bytes();
		match self {
			AnyString::Ascii(x) => x.remove(idx).as_char(),
			AnyString::Utf8(x) => x.remove(idx),
			AnyString::Utf16(x) => x.remove(idx),
			AnyString::Utf32(x) => x.remove(idx),
		}
	}

	/// Retains only the characters specified by the predicate.
	///
	/// In other words, remove all characters `c` such that `f(c)` returns `false`.
	/// This method operates in place, visiting each character exactly once in the
	/// original order, and preserves the order of the retained characters.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyString;
	/// let mut s = AnyString::from("f_o_ob_ar");
	///
	/// s.retain(|c| c != '_');
	///
	/// assert_eq!(s, "foobar");
	/// ```
	///
	/// Because the elements are visited exactly once in the original order,
	/// external state may be used to decide which elements to keep.
	///
	/// ```
	/// use anystr::AnyString;
	/// let mut s = AnyString::from("abcde");
	/// let keep = [false, true, true, false, true];
	/// let mut iter = keep.iter();
	/// s.retain(|_| *iter.next().unwrap());
	/// assert_eq!(s, "bce");
	/// ```
	#[inline]
	pub fn retain<F>(&mut self, mut f: F) where F: FnMut(char) -> bool {
		match self {
			AnyString::Ascii(x) => {
				let mut new_string = AsciiString::new();
				for ch in x.chars() {
					let keep = f(ch.as_char());
					if keep {
						new_string.push(ch);
					}
				}
				*x = new_string;
			},
			AnyString::Utf8(x) => x.retain(f),
			AnyString::Utf16(x) => x.retain(f),
			AnyString::Utf32(x) => x.retain(f),
		}
	}

	/// Inserts a character into this `AnyString` at a byte position.
	///
	/// This is an *O*(*n*) operation as it requires copying every element in the
	/// buffer.
	///
	/// # Panics
	///
	/// Panics if `idx` is larger than the `AnyString`'s length, or if it does not
	/// lie on a [char][`prim@char`] boundary.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::{AnyString, Encoding};
	/// let mut s = AnyString::with_capacity(3, Encoding::Utf8);
	///
	/// s.insert(0, 'f').unwrap();
	/// s.insert(1, 'o').unwrap();
	/// s.insert(2, 'o').unwrap();
	///
	/// assert_eq!(s, "foo");
	/// ```
	#[inline]
	pub fn insert(&mut self, idx: usize, ch: char) -> Result<(), ConversionError> {
		use ascii::ToAsciiChar;
		let idx = idx / self.get_encoding().bytes();
		match self {
			AnyString::Ascii(x) => Ok(x.insert(idx, ch.to_ascii_char().map_err(AsciiError::from)?)),
			AnyString::Utf8(x) => Ok(x.insert(idx, ch)),
			AnyString::Utf16(x) => Ok(x.insert(idx, ch)),
			AnyString::Utf32(x) => Ok(x.insert(idx, ch)),
		}
	}

	/// Inserts a string slice into this `AnyString` at a byte position.
	///
	/// This is an *O*(*n*) operation as it requires copying every element in the
	/// buffer.
	///
	/// # Panics
	///
	/// Panics if `idx` is larger than the `AnyString`'s length, or if it does not
	/// lie on a [`char`] boundary.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyString;
	/// let mut s = AnyString::from("bar");
	///
	/// s.insert_str(0, "foo").unwrap();
	///
	/// assert_eq!(s, "foobar");
	/// ```
	#[inline]
	pub fn insert_str<T: AsRef<str> + ?Sized>(&mut self, idx: usize, string: &T) -> Result<(), ConversionError> {
		let idx = idx / self.get_encoding().bytes();
		match self {
			AnyString::Ascii(x) => {
				let ascii_str = AsciiStr::from_ascii(string.as_ref().as_bytes()).map_err(AsciiError::from)?;
				Ok(x.insert_str(idx, ascii_str))
			}
			AnyString::Utf8(x) => Ok(x.insert_str(idx, string.as_ref())),
			AnyString::Utf16(x) => Ok(x.insert_utfstr(idx, Utf16String::from(string.as_ref()).as_ref())),
			AnyString::Utf32(x) => Ok(x.insert_utfstr(idx, Utf32String::from(string.as_ref()).as_ref())),
		}
	}

	/// Splits the string into two at the given byte index.
	///
	/// Returns a newly allocated `AnyString`. `self` contains bytes `[0, at)`, and
	/// the returned `AnyString` contains bytes `[at, len)`. `at` must be on a [`char`]
	/// boundary.
	///
	/// Note that the capacity of `self` does not change.
	///
	/// # Panics
	///
	/// Panics if `at` is not on a [`char`] boundary, or if it is beyond the end
	/// of the string.
	///
	/// # Examples
	///
	/// ```
	/// # fn main() {
	/// use anystr::AnyString;
	/// let mut hello = AnyString::from("Hello, World!");
	/// let world = hello.split_off(7);
	/// assert_eq!(hello, "Hello, ");
	/// assert_eq!(world, "World!");
	/// # }
	/// ```
	pub fn split_off(&mut self, at: usize) -> Self {
		let at = at / self.get_encoding().bytes();
		match self {
			AnyString::Ascii(x) => {
				let mut new_string = AsciiString::with_capacity(x.len() - at);
				let slice = &x[at..x.len()];
				new_string.push_str(slice);
				x.truncate(at);

				AnyString::Ascii(new_string)
			}
			AnyString::Utf8(x) => AnyString::Utf8(x.split_off(at)),
			AnyString::Utf16(x) => AnyString::Utf16(x.split_off(at)),
			AnyString::Utf32(x) => AnyString::Utf32(x.split_off(at)),
		}
	}

	/// Takes a reference to this string, converting it to an [`AnyStr`]
	#[inline]
	pub fn as_any_str(&self) -> AnyStr {
		match self {
			AnyString::Ascii(x) => AnyStr::Ascii(x.as_ref()),
			AnyString::Utf8(x) => AnyStr::Utf8(x.as_ref()),
			AnyString::Utf16(x) => AnyStr::Utf16(x.as_ref()),
			AnyString::Utf32(x) => AnyStr::Utf32(x.as_ref()),
		}
	}

	/// Returns an iterator over the [`char`]s of this string.
	#[inline]
	pub fn chars(&self) -> AnyChars {
		match self {
			AnyString::Ascii(x) => AnyChars::Ascii(x.chars()),
			AnyString::Utf8(x) => AnyChars::Utf8(x.chars()),
			AnyString::Utf16(x) => AnyChars::Utf16(x.chars()),
			AnyString::Utf32(x) => AnyChars::Utf32(x.chars()),
		}
	}
}

#[cfg(feature = "alloc")]
impl From<AnyStr<'_>> for AnyString {
	fn from(value: AnyStr<'_>) -> Self {
		value.to_any_string()
	}
}

#[cfg(feature = "alloc")]
impl From<AsciiString> for AnyString {
	fn from(value: AsciiString) -> Self {
		Self::Ascii(value)
	}
}

#[cfg(feature = "alloc")]
impl From<String> for AnyString {
	fn from(value: String) -> Self {
		Self::Utf8(value)
	}
}

#[cfg(feature = "alloc")]
impl From<Utf16String> for AnyString {
	fn from(value: Utf16String) -> Self {
		Self::Utf16(value)
	}
}

#[cfg(feature = "alloc")]
impl From<Utf32String> for AnyString {
	fn from(value: Utf32String) -> Self {
		Self::Utf32(value)
	}
}

#[cfg(feature = "alloc")]
impl From<&AsciiStr> for AnyString {
	fn from(value: &AsciiStr) -> Self {
		use alloc::borrow::ToOwned;
		Self::Ascii(value.to_owned())
	}
}

#[cfg(feature = "alloc")]
impl From<&str> for AnyString {
	fn from(value: &str) -> Self {
		use alloc::borrow::ToOwned;
		Self::Utf8(value.to_owned())
	}
}

#[cfg(feature = "alloc")]
impl From<&Utf16Str> for AnyString {
	fn from(value: &Utf16Str) -> Self {
		use alloc::borrow::ToOwned;
		Self::Utf16(value.to_owned())
	}
}

#[cfg(feature = "alloc")]
impl From<&Utf32Str> for AnyString {
	fn from(value: &Utf32Str) -> Self {
		use alloc::borrow::ToOwned;
		Self::Utf32(value.to_owned())
	}
}

#[cfg(feature = "alloc")]
impl PartialEq<&str> for AnyString {
	fn eq(&self, other: &&str) -> bool {
		match self {
			AnyString::Ascii(x) => x.eq(other),
			AnyString::Utf8(x) => x.eq(other),
			AnyString::Utf16(x) => x.eq(other),
			AnyString::Utf32(x) => x.eq(other),
		}
	}
}

#[cfg(feature = "alloc")]
impl core::ops::Add<AnyString> for AnyString {
	type Output = AnyString;

	fn add(mut self, rhs: Self) -> Self::Output {
		use core::ops::AddAssign;
		self.add_assign(rhs);
		self
	}
}

#[cfg(feature = "alloc")]
impl core::ops::AddAssign<AnyString> for AnyString {
	fn add_assign(&mut self, rhs: AnyString) {
		match rhs {
			AnyString::Ascii(x) => {
				self.push_str(&x).expect("Conversion error");
			}
			AnyString::Utf8(x) => {
				self.push_str(&x).expect("Conversion error");
			}
			AnyString::Utf16(x) => {
				for ch in x.chars() {
					self.push(ch).expect("Conversion error");
				}
			}
			AnyString::Utf32(x) => {
				for ch in x.chars() {
					self.push(ch).expect("Conversion error");
				}
			}
		}
	}
}

/// An iterator over the characters of [`AnyStr`] or [`AnyString`].
///
/// Can be constructed by calling either [`AnyStr::chars`] or [`AnyString::chars`]
pub enum AnyChars<'iter> {
	Ascii(ascii::Chars<'iter>),
	Utf8(core::str::Chars<'iter>),
	Utf16(widestring::utfstr::CharsUtf16<'iter>),
	Utf32(widestring::utfstr::CharsUtf32<'iter>),
}

impl<'iter> Iterator for AnyChars<'iter> {
	type Item = char;
	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		match self {
			AnyChars::Ascii(x) => x.next().map(|ch| ch.as_char()),
			AnyChars::Utf8(x) => x.next(),
			AnyChars::Utf16(x) => x.next(),
			AnyChars::Utf32(x) => x.next(),
		}
	}
	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		match self {
			AnyChars::Ascii(x) => x.size_hint(),
			AnyChars::Utf8(x) => x.size_hint(),
			AnyChars::Utf16(x) => x.size_hint(),
			AnyChars::Utf32(x) => x.size_hint(),
		}
	}
}

/// An enum that encapsulates a referenced string type and encoding while "re-exporting"
/// many of the methods found on a `str`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum AnyStr<'a> {
	Ascii(&'a AsciiStr),
	Utf8(&'a str),
	Utf16(&'a Utf16Str),
	Utf32(&'a Utf32Str)
}

impl<'a> AnyStr<'a> {
	/// Returns the underlying [string encoding][`Encoding`].
	#[inline]
	pub fn get_encoding(&self) -> Encoding {
		match self {
			AnyStr::Ascii(_) => Encoding::Ascii,
			AnyStr::Utf8(_) => Encoding::Utf8,
			AnyStr::Utf16(_) => Encoding::Utf16,
			AnyStr::Utf32(_) => Encoding::Utf32,
		}
	}

	/// Returns the length of `self`.
	///
	/// This length is in bytes, not [`char`][s or graphemes. In other words,
	/// it might not be what a human considers the length of the string.
	///
	/// [`char`]: prim@char
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyStr;
	/// let len = AnyStr::Utf8("foo").len();
	/// assert_eq!(3, len);
	///
	/// assert_eq!("ƒoo".len(), 4); // fancy f!
	/// assert_eq!("ƒoo".chars().count(), 3);
	/// ```
	#[inline]
	#[must_use]
	pub fn len(&self) -> usize {
		let len = match self {
			AnyStr::Ascii(x) => x.len(),
			AnyStr::Utf8(x) => x.len(),
			AnyStr::Utf16(x) => x.len(),
			AnyStr::Utf32(x) => x.len(),
		};
		self.get_encoding().bytes() * len
	}

	/// Returns `true` if `self` has a length of zero bytes.
	///
	/// # Examples
	///
	/// ```
	/// use anystr::AnyStr;
	/// let s = AnyStr::Utf8("");
	/// assert!(s.is_empty());
	///
	/// let s = AnyStr::Utf8("not empty");
	/// assert!(!s.is_empty());
	/// ```
	#[inline]
	#[must_use]
	pub fn is_empty(&self) -> bool {
		match self {
			AnyStr::Ascii(x) => x.is_empty(),
			AnyStr::Utf8(x) => x.is_empty(),
			AnyStr::Utf16(x) => x.is_empty(),
			AnyStr::Utf32(x) => x.is_empty(),
		}
	}

	/// Returns an iterator over the [`char`]s of this string.
	#[inline]
	pub fn chars(&self) -> AnyChars {
		match self {
			AnyStr::Ascii(x) => AnyChars::Ascii(x.chars()),
			AnyStr::Utf8(x) => AnyChars::Utf8(x.chars()),
			AnyStr::Utf16(x) => AnyChars::Utf16(x.chars()),
			AnyStr::Utf32(x) => AnyChars::Utf32(x.chars()),
		}
	}

	/// Converts `self` into an owned string.
	#[cfg(feature = "alloc")]
	pub fn to_any_string(&self) -> AnyString {
		use alloc::borrow::ToOwned;
		match self {
			AnyStr::Ascii(x) => AnyString::Ascii(AsciiStr::to_owned(x)),
			AnyStr::Utf8(x) => AnyString::Utf8(str::to_owned(x)),
			AnyStr::Utf16(x) => AnyString::Utf16(Utf16Str::to_owned(x)),
			AnyStr::Utf32(x) => AnyString::Utf32(Utf32Str::to_owned(x)),
		}
	}
}

#[cfg(feature = "alloc")]
impl<'a> From<&'a AnyString> for AnyStr<'a> {
	fn from(value: &'a AnyString) -> Self {
		value.as_any_str()
	}
}

impl PartialEq<str> for AnyStr<'_> {
	fn eq(&self, other: &str) -> bool {
		match self {
			AnyStr::Ascii(x) => (*x).eq(other),
			AnyStr::Utf8(x) => (*x).eq(other),
			AnyStr::Utf16(x) => x.eq(other),
			AnyStr::Utf32(x) => x.eq(other),
		}
	}
}

impl<'a> From<&'a AsciiStr> for AnyStr<'a> {
	fn from(value: &'a AsciiStr) -> Self {
		Self::Ascii(value)
	}
}

impl<'a> From<&'a str> for AnyStr<'a> {
	fn from(value: &'a str) -> Self {
		Self::Utf8(value)
	}
}

impl<'a> From<&'a Utf16Str> for AnyStr<'a> {
	fn from(value: &'a Utf16Str) -> Self {
		Self::Utf16(value)
	}
}

impl<'a> From<&'a Utf32Str> for AnyStr<'a> {
	fn from(value: &'a Utf32Str) -> Self {
		Self::Utf32(value)
	}
}