// Permission is hereby granted, free of charge, to any
// person obtaining a copy of this software and associated
// documentation files (the "Software"), to deal in the
// Software without restriction, including without
// limitation the rights to use, copy, modify, merge,
// publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following
// conditions:

// The above copyright notice and this permission notice
// shall be included in all copies or substantial portions
// of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
// ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
// TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
// PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
// SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
// IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.

use std::fmt;
use std::ffi::{CStr, NulError};

use bincode::Error as BincodeError;

use gdbm_sys;

type ErrorCode = u32;

//TODO: merge with Error
/// An error originating in the gdbm C library.
#[derive(Debug)]
pub enum GdbmError {
    /// The file was not a valid database.
    InvalidDatabase,
    /// Database is in inconsistent state and needs recovery.
    NeedsRecovery,
    /// The end of the file was reached unexpectedly. This probably indicates
    /// Database corruption.
    UnexpectedEOF,
    /// Another gdbm error.
    Other(ErrorCode),
}

/// An error when interacting with a database.
#[derive(Debug)]
pub enum Error {
    /// The path was not a valid C String.
    InvalidPath,
    /// The key passed to `store_safe` existed in the database.
    KeyExists,
    /// No item with this key exists in the database.
    NoRecord,
    /// An error occured while encoding to or decoding from binary.
    Bincode(BincodeError),
    /// An error originating in the gdbm C library.
    Internal(GdbmError),
}

/// The result type for Database operations.
pub type GdbmResult<T> = Result<T, Error>;

impl GdbmError {
    /// Returns the last error reported by gdbm in the current thread.
    pub (crate) fn from_last() -> Self {
        last_errno().into()
    }
}

impl Error {
    /// Returns the last error reported by gdbm in the current thread.
    pub (crate) fn from_last() -> Self {
        last_errno().into()
    }

    /// Returns `true` iff `self` is the `NoRecord` enum member.
    pub fn is_no_record(&self) -> bool {
        match *self {
            Error::NoRecord => true,
            _ => false
        }
    }
}

#[doc(hidden)]
impl fmt::Display for GdbmError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            GdbmError::InvalidDatabase => write!(f, "The file is not a valid database"),
            GdbmError::NeedsRecovery => write!(f, "The database is corrupted"),
            GdbmError::UnexpectedEOF => write!(f, "Unexpected EOF in database"),
            GdbmError::Other(code) => unsafe {
                let err_ptr = gdbm_sys::gdbm_strerror(code as i32);
                let err_string = CStr::from_ptr(err_ptr);
                write!(f, "{}", err_string.to_string_lossy())
            },
        }
    }
}

#[doc(hidden)]
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Internal(ref e) => e.fmt(f),
            Error::InvalidPath => write!(f, "Invalid path (interior null byte)"),
            Error::KeyExists => write!(f, "key already exists in database"),
            Error::NoRecord => write!(f, "key does not exist in database"),
            Error::Bincode(ref e) => e.fmt(f),
        }
    }
}

#[doc(hidden)]
impl From<u32> for Error {
    fn from(src: u32) -> Error {
        match src {
            errno if errno == gdbm_sys::GDBM_ITEM_NOT_FOUND => Error::NoRecord,
            errno => Error::Internal(errno.into()),
        }
    }
}

#[doc(hidden)]
impl From<u32> for GdbmError {
    fn from(src: u32) -> GdbmError {
        match src {
            errno if errno == gdbm_sys::GDBM_EMPTY_DATABASE => GdbmError::InvalidDatabase,
            errno if errno == gdbm_sys::GDBM_NEED_RECOVERY => GdbmError::NeedsRecovery,
            other => GdbmError::Other(other),
        }
    }
}

#[doc(hidden)]
impl From<NulError> for Error {
    fn from(_src: NulError) -> Error {
        Error::InvalidPath
    }
}

#[doc(hidden)]
impl From<GdbmError> for Error {
    fn from(src: GdbmError) -> Error {
        Error::Internal(src)
    }
}

#[doc(hidden)]
impl From<BincodeError> for Error {
    fn from(src: BincodeError) -> Error {
        Error::Bincode(src)
    }
}

#[doc(hidden)]
pub fn last_errno() -> u32 {
    unsafe {
        let err_loc = gdbm_sys::gdbm_errno_location();
        *err_loc as u32
    }
}
