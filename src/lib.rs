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

extern crate libc;
extern crate serde;
extern crate bincode;
#[cfg(test)]
extern crate tempdir;
#[cfg(test)]
#[macro_use]
extern crate serde_derive;

mod gdbm_sys;
mod error;

use std::ops::Drop;
use std::default::Default;
use std::path::Path;
use std::slice;
use std::ffi::CString;
use std::os::unix::ffi::OsStrExt;

use serde::{Serialize, Deserialize};
use serde::de::DeserializeOwned;

use error::{Error, GdbmError, GdbmResult, last_errno};

#[derive(Debug)]
pub struct Database {
    handle: gdbm_sys::GDBM_FILE,
}

#[derive(Debug)]
pub struct ReadOnlyDb(Database);

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

#[derive(Debug)]
pub struct Entry<'a> {
    datum: gdbm_sys::datum,
    slice: &'a [u8],
}

#[derive(Debug)]
pub struct Key<'a>(Entry<'a>);

#[derive(Debug)]
pub struct Iter<'a> {
    db: &'a Database,
    nxt_key: Option<gdbm_sys::datum>,
}

impl<'a> Iter<'a> {
    fn new(db: &'a Database) -> Self {
        let firstkey = unsafe { gdbm_sys::gdbm_firstkey(db.handle) };
        let nxt_key = if firstkey.dptr.is_null() { None } else { Some(firstkey) };
        Iter { db, nxt_key }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = (Key<'a>, Entry<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(d) = self.nxt_key.take() {
            let value_d = unsafe { gdbm_sys::gdbm_fetch(self.db.handle, d) };
            let nxt = unsafe { gdbm_sys::gdbm_nextkey(self.db.handle, d) };
            //TODO: check this error :{
            if value_d.dptr.is_null() {
                return None
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

impl<'a> Entry<'a> {
    pub fn new(datum: gdbm_sys::datum) -> Self {
        let slice = unsafe {
            slice::from_raw_parts(datum.dptr as *const u8,
                                  datum.dsize as usize)
        };
        Entry { datum, slice }
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.slice
    }

    pub fn as_type<'de, T>(&'de self) -> Result<T, bincode::Error>
        where T: Deserialize<'de>
    {
        bincode::deserialize(self.slice)
    }

    //TODO: remove this
    pub fn into_type<T>(self) -> Result<T, bincode::Error>
        where T: DeserializeOwned
    {
        bincode::deserialize(self.slice)
    }
}

impl<'a> Key<'a> {
    pub fn as_bytes(&self) -> &[u8] {
        self.0.slice
    }
}

impl<'a> Drop for Entry<'a> {
    fn drop(&mut self) {
        unsafe { libc::free(self.datum.dptr as *mut libc::c_void); }
    }
}

impl Drop for Database {
    fn drop(&mut self) {
        unsafe { gdbm_sys::gdbm_close(self.handle) }
    }
}

impl<'a> Drop for Iter<'a> {
    fn drop(&mut self) {
        if let Some(datum) = self.nxt_key {
            unsafe { libc::free(datum.dptr as *mut libc::c_void); }
        }
    }
}

impl GdbmOpener {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn create_if_needed(&mut self, create: bool) -> &mut Self {
        self.create = create; self
    }

    pub fn overwrite(&mut self, overwrite: bool) -> &mut Self {
        self.overwrite = overwrite; self
    }

    pub fn sync(&mut self, sync: bool) -> &mut Self {
        self.sync = sync; self
    }

    pub fn no_lock(&mut self, no_lock: bool) -> &mut Self {
        self.no_lock = no_lock; self
    }

    pub fn no_mmap(&mut self, no_mmap: bool) -> &mut Self {
        self.no_mmap = no_mmap; self
    }

    pub fn open<P: AsRef<Path>>(&self, path: P) -> GdbmResult<Database> {
        let path = path.as_ref();
        let handle = self.gdbm_open(&path)?;
        Ok(Database { handle })
    }

    pub fn open_readonly<P: AsRef<Path>>(&mut self, path: P)
        -> GdbmResult<ReadOnlyDb> {
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

        if self.sync { flags |= gdbm_sys::GDBM_SYNC as i32 }
        if self.no_lock { flags |= gdbm_sys::GDBM_NOLOCK as i32 }
        if self.no_mmap { flags |= gdbm_sys::GDBM_NOMMAP as i32 }

        eprintln!("opening with mode {}", flags);
        let handle = unsafe {
            gdbm_sys::gdbm_open(path_ptr,
                                self.block_size,
                                flags,
                                DEFAULT_MODE,
                                None)
        };

        if handle.is_null() {
            Err(GdbmError::from_last().into())
        } else {
            Ok(handle)
        }
    }
}

impl Database {
    pub fn store<T>(&mut self, key: &[u8], value: &T) -> GdbmResult<()>
        where T: ?Sized + Serialize
    {
        self.store_impl(key, value, true).map(|_| ())
    }

    pub fn store_safe<T>(&mut self, key: &[u8], value: &T) -> GdbmResult<()>
        where T: ?Sized + Serialize
    {
        let r = self.store_impl(key, value, false)?;
        if r == 1 {
            Err(Error::KeyExists)
        } else {
            Ok(())
        }
    }

    fn store_impl<T>(&mut self, key: &[u8], value: &T, replace: bool) -> GdbmResult<i32>
        where T: ?Sized + Serialize
    {
        let bytes = bincode::serialize(value)?;
        let key_d: gdbm_sys::datum = key.into();

        let value_d = gdbm_sys::datum {
            dptr: bytes.as_ptr() as *mut i8,
            dsize: bytes.len() as i32,
        };

        let flag = if replace { gdbm_sys::GDBM_REPLACE } else { gdbm_sys::GDBM_INSERT };

        let result = unsafe {
            gdbm_sys::gdbm_store(self.handle, key_d, value_d, flag as i32)
        };

        if result == -1 {
            Err(GdbmError::from_last().into())
        } else {
            Ok(result)
        }
    }

    pub fn fetch(&self, key: &[u8]) -> GdbmResult<Entry> {
        let key_d: gdbm_sys::datum = key.into();
        let result = unsafe { gdbm_sys::gdbm_fetch(self.handle, key_d) };
        // memory will be cleaned up in Entry::drop
        let _ = Entry::new(key_d);

        if result.dptr.is_null() {
            Err(GdbmError::from_last().into())
        } else {
            Ok(Entry::new(result))
        }
    }

    pub fn remove(&self, key: &[u8]) -> GdbmResult<()> {
        let result = unsafe { gdbm_sys::gdbm_delete(self.handle, key.into()) };
        if result != 0 {
            Err(GdbmError::from_last().into())
        } else {
            Ok(())
        }
    }

    /// Returns the number of items in this database. This is not cached.
    pub fn count(&self) -> GdbmResult<u64> {
        let mut count = 0_u64;
        let count_ptr: *mut u64 = &mut count;
        let r = unsafe { gdbm_sys::gdbm_count(self.handle, count_ptr) };
        if r == -1 {
            Err(GdbmError::from_last().into())
        } else {
            Ok(count)
        }
    }

    pub fn iter<'a>(&'a self) -> Iter<'a> {
        Iter::new(self)
    }

    pub fn contains_key(&self, key: &[u8]) -> GdbmResult<bool> {
        let key_d: gdbm_sys::datum = key.into();
        let result = unsafe { gdbm_sys::gdbm_exists(self.handle, key_d) };
        // memory will be cleaned up in Entry::drop
        let _ = Entry::new(key_d);

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

    pub fn flush(&self) {
        //TODO: this should be failable, but docs don't show how we get the error :|
        unsafe { gdbm_sys::gdbm_sync(self.handle) }
    }

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
}

impl ReadOnlyDb {
    pub fn fetch(&self, key: &[u8]) -> GdbmResult<Entry> {
        self.0.fetch(key)
    }

    /// Returns the number of items in this database. This is not cached.
    pub fn count(&self) -> GdbmResult<u64> {
        self.0.count()
    }

    pub fn iter<'a>(&'a self) -> Iter<'a> {
        self.0.iter()
    }
}

//TODO: move me into sys_gdbm
impl<'a> From<&'a [u8]> for gdbm_sys::datum {
    fn from(src: &'a [u8]) -> gdbm_sys::datum {
        gdbm_sys::datum {
            dptr: src.as_ptr() as *mut i8,
            dsize: src.len() as i32,
        }
    }
}

//TODO: use umask
const DEFAULT_MODE: i32 = 0o666;

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
            let s: Vec<i32> = entry.into_type().unwrap();
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
            db.store(&vec![i as u8], &i)
                .unwrap();
        }

        {
            let iter = db.iter();
            assert_eq!(5, iter.count());
        }

        let iter = db.iter();
        let sum = iter.fold(0, |acc, (_,ent)| acc + ent.as_type::<i32>().unwrap());
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

