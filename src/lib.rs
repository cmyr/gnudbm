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
#![warn(missing_docs)]

//! Gnudbm is an ergonomic, idiomatic wrapper for [gdbm].
//!
//! With built in support for [Serde] and [bincode], It provides fast and easy
//! local key/value storage of any type implementing [`Serialize`].
//!
//! [gdbm]: http://puszcza.gnu.org.ua/software/gdbm/
//! [serde]: https://serde.rs
//! [bincode]: https://github.com/TyOverby/bincode
//! [`Serialize`]: https://serde.rs/impl-serialize.html
//!
//! # Examples
//!
//! Creating a new database:
//!
//! ```no_run
//! # use std::path::PathBuf;
//! # use gnudbm::*;
//! let db_path = PathBuf::from("path/to/my.db");
//! let mut db = GdbmOpener::new()
//!     .create_if_needed(true)
//!     .open(&db_path)
//!     .expect("db creation failed");
//! ```
//!
//! Use with Serde:
//!
//! ```no_run
//! # #[macro_use] extern crate serde_derive;
//! # extern crate serde;
//! # extern crate gnudbm;
//! # use gnudbm::*;
//! use serde::{Serialize, Deserialize};
//! # fn main() {
//! # let mut db = Database::dummy();
//!
//! #[derive(Serialize, Deserialize)]
//! struct MyStruct<'a> {
//!     name: &'a str,
//!     counts: Vec<u64>,
//! }
//!
//! let name: String = "Colin".into();
//! let value = MyStruct {
//!     name: &name,
//!     counts: vec![4, 2, 0],
//! };
//!
//! // 'db' is a previously configured database
//! db.store("my key".as_bytes(), &value).unwrap();
//!
//! let entry = db.fetch("my key".as_bytes()).unwrap();
//! let fetched: MyStruct = entry.as_type().unwrap();
//!
//! assert_eq!(value.name, fetched.name);
//! # }
//! ```

extern crate bincode;
extern crate libc;
extern crate serde;
#[cfg(test)]
#[macro_use]
extern crate serde_derive;
#[cfg(test)]
extern crate tempdir;

mod gdbm_sys;
mod error;

use std::ops::Drop;
use std::default::Default;
use std::path::Path;
use std::slice;
use std::ffi::CString;
use std::os::unix::ffi::OsStrExt;

use serde::{Deserialize, Serialize};

use error::last_errno;
pub use error::{Error, GdbmError, GdbmResult};

//TODO: use umask
const DEFAULT_MODE: i32 = 0o666;

/// A read/write connection to a gdbm database.
#[derive(Debug)]
pub struct Database {
    handle: gdbm_sys::GDBM_FILE,
}

/// A readonly connection to a gdbm database.
///
/// This type only exposes non-modifying methods, to avoid having to handle
/// errors around attempting to modify a database opened in read-only mode.
#[derive(Debug)]
pub struct ReadOnlyDb(Database);

/// A builder used to open gdbm files.
#[derive(Debug, Default)]
pub struct GdbmOpener {
    sync: bool,
    no_lock: bool,
    no_mmap: bool,
    create: bool,
    overwrite: bool,
    readonly: bool,
    block_size: i32,
}

/// An entry in a gdbm database.
///
/// This type represents arbitrary data retrieved from the database.
#[derive(Debug)]
pub struct Entry<'a> {
    datum: gdbm_sys::datum,
    slice: &'a [u8],
}

/// A key retrieved from a gdbm database.
///
/// This type is only used as the return value of `Database::iter`. It is
/// distinct from [`Entry`] for the sake of clarity.
#[derive(Debug)]
pub struct Key<'a>(Entry<'a>);

/// An iterator over keys and values in a gdbm database.
#[derive(Debug)]
pub struct Iter<'a> {
    db: &'a Database,
    nxt_key: Option<gdbm_sys::datum>,
}

impl Database {
    /// Inserts a key value pair into the database, replacing any existing
    /// value for that key.
    ///
    /// Returns an [`Error`] if the store fails. The only reason this might happen
    /// is if there is a problem writing to disk, which is likely not recoverable.
    ///
    /// [`Error`]: error/enum.Error.html
    ///
    /// ```no_run
    /// # use gnudbm::*;
    /// # let mut db = Database::dummy();
    /// let key = "my key";
    /// let value = "my value";
    /// db.store(key.as_bytes(), value).unwrap();
    /// ```
    pub fn store<T>(&mut self, key: &[u8], value: &T) -> GdbmResult<()>
    where
        T: ?Sized + Serialize,
    {
        self.store_impl(key, value, true).map(|_| ())
    }

    /// Inserts a key value pair into the database, failing of the key already
    /// exists.
    ///
    /// Returns an [`Error`] if the store fails, including if it fails because the
    /// key already exists.
    ///
    /// [`Error`]: error/enum.Error.html
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use gnudbm::*;
    /// # let mut db = Database::dummy();
    /// let key = "my key";
    /// let value = "my value";
    /// db.store_safe(key.as_bytes(), value).unwrap();
    ///
    /// // second store will fail
    /// assert!(db.store_safe(key.as_bytes(), value).is_err());
    /// ```
    pub fn store_safe<T>(&mut self, key: &[u8], value: &T) -> GdbmResult<()>
    where
        T: ?Sized + Serialize,
    {
        let r = self.store_impl(key, value, false)?;
        if r == 1 {
            Err(Error::KeyExists)
        } else {
            Ok(())
        }
    }

    fn store_impl<T>(&mut self, key: &[u8], value: &T, replace: bool) -> GdbmResult<i32>
    where
        T: ?Sized + Serialize,
    {
        let bytes = bincode::serialize(value)?;
        let key_d: gdbm_sys::datum = key.into();

        let value_d = gdbm_sys::datum {
            dptr: bytes.as_ptr() as *mut i8,
            dsize: bytes.len() as i32,
        };

        let flag = if replace {
            gdbm_sys::GDBM_REPLACE
        } else {
            gdbm_sys::GDBM_INSERT
        };

        let result = unsafe { gdbm_sys::gdbm_store(self.handle, key_d, value_d, flag as i32) };

        if result == -1 {
            Err(GdbmError::from_last().into())
        } else {
            Ok(result)
        }
    }

    /// Attempts to fetch an item from the database.
    ///
    /// Returns an [`Entry`] if `key` exists in the database. Returns an
    /// [`Error`] if the key does not exist, or if an error occurs while
    /// reading the database.
    ///
    /// [`Entry`]: struct.Entry.html
    /// [`Error`]: error/enum.Error.html
    ///
    /// ```no_run
    /// # use gnudbm::*;
    /// # let mut db = Database::dummy();
    /// let key = "my key";
    /// let value = "my value";
    /// db.store(key.as_bytes(), &value).unwrap();
    ///
    /// let entry = db.fetch(key.as_bytes()).unwrap();
    /// let as_str: &str = entry.as_type().unwrap();
    ///
    /// assert_eq!(as_str, value);
    /// ```
    pub fn fetch(&self, key: &[u8]) -> GdbmResult<Entry> {
        let key_d = key.into();
        let result = unsafe { gdbm_sys::gdbm_fetch(self.handle, key_d) };

        if result.dptr.is_null() {
            Err(GdbmError::from_last().into())
        } else {
            Ok(Entry::new(result))
        }
    }

    /// Removes an entry from the database.
    ///
    /// Returns an [`Error`] if there is a problem with the database file.
    ///
    /// [`Error`]: error/enum.Error.html
    pub fn remove(&self, key: &[u8]) -> GdbmResult<()> {
        let key_d = key.into();
        let result = unsafe { gdbm_sys::gdbm_delete(self.handle, key_d) };
        if result != 0 {
            Err(GdbmError::from_last().into())
        } else {
            Ok(())
        }
    }

    /// Counts the number of items in this database. This is not cached.
    ///
    /// Returns the total number of items in the database as a u64, or
    /// an [`Error`] if there was a problem reading the database.
    ///
    /// [`Error`]: error/enum.Error.html
    /// # Examples
    ///
    /// ```no_run
    /// # use gnudbm::*;
    /// # let mut db = Database::dummy();
    /// for i in 0..100 {
    ///     let key = format!("key {}", i);
    ///     let value = format!("value {}", i);
    ///     db.store(key.as_bytes(), &value).unwrap();
    /// }
    ///
    /// assert_eq!(db.count().unwrap(), 100);
    /// ```
    pub fn count(&self) -> GdbmResult<usize> {
        let mut count = 0_u64;
        let count_ptr: *mut u64 = &mut count;
        let r = unsafe { gdbm_sys::gdbm_count(self.handle, count_ptr) };
        if r == -1 {
            Err(GdbmError::from_last().into())
        } else {
            Ok(count as usize)
        }
    }

    /// Returns an iterator over the keys and values in this database.
    /// The iterator's element type is `(`[`Key`], [`Entry`]`)`.
    ///
    /// [`Key`]: struct.Key.html
    /// [`Entry`]: struct.Entry.html
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use gnudbm::*;
    /// # let mut db = Database::dummy();
    /// assert_eq!(db.count().unwrap(), db.iter().count());
    /// ```
    pub fn iter<'a>(&'a self) -> Iter<'a> {
        Iter::new(self)
    }

    /// Checks the database for the existence of `key`.
    ///
    /// Returns an [`Error`] if there was a problem reading the database file,
    /// otherwise returns a `true` if the key is present in the database.
    ///
    /// [`Error`]: error/enum.Error.html
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use gnudbm::*;
    /// # let mut db = Database::dummy();
    /// let key = "my key";
    /// let value = "my value";
    /// db.store_safe(key.as_bytes(), &value).unwrap();
    ///
    /// assert!(db.contains_key(key.as_bytes()).unwrap());
    /// assert!(!db.contains_key("missing key".as_bytes()).unwrap());
    /// ```
    pub fn contains_key(&self, key: &[u8]) -> GdbmResult<bool> {
        let key_d: gdbm_sys::datum = key.into();
        let result = unsafe { gdbm_sys::gdbm_exists(self.handle, key_d) };

        if result == 0 {
            let errno = last_errno();
            if errno != gdbm_sys::GDBM_NO_ERROR {
                Err(errno.into())
            } else {
                Ok(false)
            }
        } else {
            Ok(true)
        }
    }

    /// Synchronizes the changes in the database with the file on disk.
    pub fn flush(&self) {
        //TODO: this should be failable, but docs don't show how we get the error :|
        unsafe { gdbm_sys::gdbm_sync(self.handle) }
    }

    /// Reorganizes the database file, potentially reducing its size on disk.
    ///
    /// # Note
    ///
    /// This is expensive, and should be used rarely. From the [gdbm docs]:
    ///
    /// > If you have had a lot of deletions and would like to shrink the
    /// > space used by the gdbm file, this function will reorganize the database.
    /// > This results, in particular, in shortening the length of a gdbm file
    /// > by removing the space occupied by deleted records.
    ///
    /// [gdbm docs]: http://puszcza.gnu.org.ua/software/gdbm/manual/gdbm.html#Reorganization
    pub fn reorganize(&mut self) -> GdbmResult<()> {
        let result = unsafe { gdbm_sys::gdbm_reorganize(self.handle) };
        if result != 0 {
            Err(Error::from_last())
        } else {
            Ok(())
        }
    }

    //TODO: setopt (probably just one fn per option)
    //TODO: fdesc? do we want to expose the file descriptor for locking?

    /// returns a dummy database for use with doctests
    #[allow(dead_code)]
    #[doc(hidden)]
    pub fn dummy() -> Database {
        use std::ptr;
        Database { handle: ptr::null_mut() }
    }
}

#[doc(hidden)]
impl Drop for Database {
    fn drop(&mut self) {
        unsafe { gdbm_sys::gdbm_close(self.handle) }
    }
}

impl ReadOnlyDb {
    /// Attempts to fetch an item from the database. See [`Database::fetch`]
    /// for more information.
    ///
    /// [`Database::fetch`]: struct.Database.html#method.fetch
    pub fn fetch(&self, key: &[u8]) -> GdbmResult<Entry> {
        self.0.fetch(key)
    }

    /// Returns the number of items in this database. This is not cached.
    pub fn count(&self) -> GdbmResult<usize> {
        self.0.count()
    }

    /// Returns an iterator over the keys and values in this database.
    /// See [`Database::iter`] for more information.
    ///
    /// [`Database::iter`]: struct.Database.html#method.iter
    pub fn iter<'a>(&'a self) -> Iter<'a> {
        self.0.iter()
    }
}

impl GdbmOpener {
    /// Create a new `GdbmOpener`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the option to create the file if it does not exist.
    ///
    /// This corresponds to gdbm's `GDBM_WRCREAT` flag.
    pub fn create_if_needed(&mut self, create: bool) -> &mut Self {
        self.create = create;
        self
    }

    /// Sets the option to overwrite any existing file. Implies `create_if_needed`.
    ///
    /// This corresponds to gdbm's `GDBM_NEWDB` flag.
    pub fn overwrite(&mut self, overwrite: bool) -> &mut Self {
        self.overwrite = overwrite;
        self
    }

    /// Sets the option to always immediately sync changes to disk.
    pub fn sync(&mut self, sync: bool) -> &mut Self {
        self.sync = sync;
        self
    }

    /// Sets the option to avoid file locking.
    pub fn no_lock(&mut self, no_lock: bool) -> &mut Self {
        self.no_lock = no_lock;
        self
    }

    /// Sets the option to disable memory mapping.
    pub fn no_mmap(&mut self, no_mmap: bool) -> &mut Self {
        self.no_mmap = no_mmap;
        self
    }

    /// Attempts to open the file at `path` with the options provided,
    /// returning a read/write database.
    pub fn open<P: AsRef<Path>>(&self, path: P) -> GdbmResult<Database> {
        let path = path.as_ref();
        let handle = self.gdbm_open(&path)?;
        Ok(Database { handle })
    }

    /// Attempts to open the file at `path` with the options provided,
    /// returning a read-only database.
    ///
    /// This ignores any settings applied by `create_if_needed` or `overwrite`.
    pub fn open_readonly<P: AsRef<Path>>(&mut self, path: P) -> GdbmResult<ReadOnlyDb> {
        self.readonly = true;
        let db = self.open(path)?;
        Ok(ReadOnlyDb(db))
    }

    fn gdbm_open(&self, path: &Path) -> GdbmResult<gdbm_sys::GDBM_FILE> {
        let path = CString::new(path.as_os_str().as_bytes())?;
        let path_ptr = path.as_ptr() as *mut i8;

        let mut flags = gdbm_sys::GDBM_WRITER as i32;
        if self.readonly {
            flags = gdbm_sys::GDBM_READER as i32;
        } else if self.overwrite {
            flags = gdbm_sys::GDBM_NEWDB as i32;
        } else if self.create {
            flags = gdbm_sys::GDBM_WRCREAT as i32;
        }

        if self.sync {
            flags |= gdbm_sys::GDBM_SYNC as i32
        }
        if self.no_lock {
            flags |= gdbm_sys::GDBM_NOLOCK as i32
        }
        if self.no_mmap {
            flags |= gdbm_sys::GDBM_NOMMAP as i32
        }

        eprintln!("opening with mode {}", flags);
        let handle =
            unsafe { gdbm_sys::gdbm_open(path_ptr, self.block_size, flags, DEFAULT_MODE, None) };

        if handle.is_null() {
            Err(GdbmError::from_last().into())
        } else {
            Ok(handle)
        }
    }
}

impl<'a> Entry<'a> {
    fn new(datum: gdbm_sys::datum) -> Self {
        let slice = unsafe { slice::from_raw_parts(datum.dptr as *const u8, datum.dsize as usize) };
        Entry { datum, slice }
    }

    /// Returns the contents of the entry as a slice of bytes.
    ///
    /// This is zero-cost; the returned slice is the memory returned by the
    /// gdbm C library.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use gnudbm::*;
    /// # let mut db = Database::dummy();
    /// let key = "my key";
    /// let value = "my value";
    /// db.store(key.as_bytes(), &value).unwrap();
    ///
    /// let entry = db.fetch(key.as_bytes()).unwrap();
    ///
    /// assert_eq!(entry.as_bytes(), value.as_bytes());
    /// ```
    pub fn as_bytes(&self) -> &[u8] {
        self.slice
    }

    /// Attempts to deserialize this entry into some type which implements
    /// [`serde::Serialize`].
    ///
    /// This can borrow data, bound to the lifetime of `self`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use gnudbm::*;
    /// # use std::collections::BTreeMap;
    /// # let mut db = Database::dummy();
    /// let key = "my key";
    ///
    /// // BTreeMap implements `Serialize` so we can insert it and parse from an entry.
    /// let value = [("hi", 5), ("you", 2), ("eye", 1)].iter()
    ///     .cloned()
    ///     .collect::<BTreeMap<&'static str, i32>>();
    /// db.store(key.as_bytes(), &value).unwrap();
    ///
    /// let entry = db.fetch(key.as_bytes()).unwrap();
    /// let as_map: BTreeMap<&str, i32> = entry.as_type().unwrap();
    ///
    /// assert_eq!(as_map.get("hi"), Some(&5));
    ///
    /// ```
    pub fn as_type<'de, T>(&'de self) -> Result<T, bincode::Error>
    where
        T: Deserialize<'de>,
    {
        bincode::deserialize(self.slice)
    }
}

#[doc(hidden)]
impl<'a> Drop for Entry<'a> {
    fn drop(&mut self) {
        if self.datum.dptr.is_null() { return };
        unsafe {
            libc::free(self.datum.dptr as *mut libc::c_void);
        }
    }
}

impl<'a> Key<'a> {
    /// Returns the contents of the key as a slice of bytes.
    pub fn as_bytes(&self) -> &[u8] {
        self.0.slice
    }
}

impl<'a> Iter<'a> {
    fn new(db: &'a Database) -> Self {
        let firstkey = unsafe { gdbm_sys::gdbm_firstkey(db.handle) };
        let nxt_key = if firstkey.dptr.is_null() {
            None
        } else {
            Some(firstkey)
        };
        Iter { db, nxt_key }
    }
}

#[doc(hidden)]
impl<'a> Iterator for Iter<'a> {
    type Item = (Key<'a>, Entry<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(d) = self.nxt_key.take() {
            let value_d = unsafe { gdbm_sys::gdbm_fetch(self.db.handle, d) };
            let nxt = unsafe { gdbm_sys::gdbm_nextkey(self.db.handle, d) };
            //TODO: check this error :{
            if value_d.dptr.is_null() {
                return None;
            }
            if !nxt.dptr.is_null() {
                self.nxt_key = Some(nxt);
            } else {
                //TODO? how do we want to handle errors in the iterator?
            }
            Some((Key(Entry::new(d)), Entry::new(value_d)))
        } else {
            None
        }
    }
}

#[doc(hidden)]
impl<'a> Drop for Iter<'a> {
    fn drop(&mut self) {
        if let Some(datum) = self.nxt_key {
            if !datum.dptr.is_null() {
                unsafe {
                    libc::free(datum.dptr as *mut libc::c_void);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempdir::TempDir;

    fn create_db(path: &Path) -> Database {
        assert!(!path.exists());
        let db = GdbmOpener::new()
            .create_if_needed(true)
            .open(&path)
            .expect("db creation failed");
        assert!(path.exists());
        db
    }

    #[test]
    fn smoke_test() {
        let dir = TempDir::new("rust_gdbm").unwrap();
        let db_path = dir.path().join("create.db");
        let mut db = create_db(&db_path);
        assert!(db_path.exists());

        db.store("my key".as_bytes(), "my value").unwrap();
        {
            let entry = db.fetch("my key".as_bytes()).unwrap();
            let s: &str = entry.as_type().unwrap();
            assert_eq!(s, "my value");
        }
    }

    #[test]
    fn test_readonly() {
        let dir = TempDir::new("rust_gdbm").unwrap();
        let db_path = dir.path().join("readonly.db");
        create_db(&db_path);
        assert!(db_path.exists());

        let _ = GdbmOpener::new()
            .open_readonly(&db_path)
            .expect("db read failed");

        let _ = GdbmOpener::new()
            .open_readonly(&db_path)
            .expect("db 2nd read failed");
    }

    #[test]
    fn test_modes() {
        let dir = TempDir::new("rust_gdbm").unwrap();
        let db_path = dir.path().join("read.db");
        assert!(!db_path.exists());

        {
            let mut db = GdbmOpener::new()
                .create_if_needed(true)
                .open(&db_path)
                .expect("db creation failed");
            db.store("read key".as_bytes(), "read value").unwrap();
            assert!(db_path.exists());
        }
        {
            assert!(db_path.exists());
            let db = GdbmOpener::new()
                .open_readonly(&db_path)
                .expect("db open failed");

            {
                let entry = db.fetch("read key".as_bytes()).unwrap();
                let s: String = entry.as_type().unwrap();
                assert_eq!(s, "read value");
            }
        }
        {
            let mut db = GdbmOpener::new()
                .open(&db_path)
                .expect("db open for write failed");

            db.store("write key".as_bytes(), "write value").unwrap();
            {
                let entry = db.fetch("write key".as_bytes()).unwrap();
                let s: String = entry.as_type().unwrap();
                assert_eq!(s, "write value");
            }
        }

        // ::New should overwrite the database
        let db = GdbmOpener::new()
            .overwrite(true)
            .open(&db_path)
            .expect("db new failed");

        let r = db.fetch("write key".as_bytes());
        assert!(r.is_err());
    }

    #[test]
    fn count() {
        let dir = TempDir::new("rust_gdbm").unwrap();
        let db_path = dir.path().join("count.db");
        let mut db = create_db(&db_path);

        assert_eq!(db.count().unwrap(), 0);
        for i in 0..5 {
            db.store(format!("key {}", i).as_bytes(), &format!("value {}", i))
                .unwrap();
        }
        assert_eq!(db.count().unwrap(), 5);
        for i in 5..10 {
            db.store(format!("key {}", i).as_bytes(), &format!("value {}", i))
                .unwrap();
        }
        assert_eq!(db.count().unwrap(), 10);
    }

    #[test]
    fn entry() {
        let dir = TempDir::new("rust_gdbm").unwrap();
        let db_path = dir.path().join("entry.db");
        let mut db = create_db(&db_path);
        // serialize some standard types
        db.store("an int".as_bytes(), &6usize).unwrap();
        {
            let entry = db.fetch("an int".as_bytes()).unwrap();
            let s: usize = entry.as_type().unwrap();
            assert_eq!(6, s);
        }

        let v = vec![4, 2, 0];
        db.store("a vec".as_bytes(), &v).unwrap();
        {
            let entry = db.fetch("a vec".as_bytes()).unwrap();
            let s: Vec<i32> = entry.as_type().unwrap();
            assert_eq!(s, v);
        }

        #[derive(Serialize, Deserialize, PartialEq, Eq, Debug)]
        struct MyStruct<'a> {
            name: &'a str,
            count: usize,
            maybe: Option<bool>,
        }

        let n = "me".to_string();
        let s = MyStruct {
            name: &n,
            count: 808,
            maybe: None,
        };

        db.store("a struct".as_bytes(), &s).unwrap();
        let entry = db.fetch("a struct".as_bytes()).unwrap();
        let r: MyStruct = entry.as_type().unwrap();
        assert_eq!(r, s);
    }

    #[test]
    fn test_iter() {
        let dir = TempDir::new("rust_gdbm").unwrap();
        let db_path = dir.path().join("iter.db");
        let mut db = create_db(&db_path);

        for i in 0..5 {
            //TODO: figure out why this crashes if i is an i32
            db.store(&vec![i as u8], &i).unwrap();
        }

        {
            let iter = db.iter();
            assert_eq!(5, iter.count());
        }

        let iter = db.iter();
        let sum = iter.fold(0, |acc, (_, ent)| acc + ent.as_type::<i32>().unwrap());
        assert_eq!(sum, (0..5).sum());
    }

    #[test]
    fn contains_delete() {
        let dir = TempDir::new("rust_gdbm").unwrap();
        let db_path = dir.path().join("contains_del.db");
        let mut db = create_db(&db_path);

        for i in 0..5 {
            db.store(format!("key {}", i).as_bytes(), &format!("value {}", i))
                .unwrap();
        }

        assert!(db.contains_key("key 1".as_bytes()).unwrap());
        assert!(!db.contains_key("key x".as_bytes()).unwrap());
        db.remove("key 1".as_bytes()).unwrap();
        assert!(!db.contains_key("key 1".as_bytes()).unwrap());
        assert!(db.contains_key("key 2".as_bytes()).unwrap());
    }
}
