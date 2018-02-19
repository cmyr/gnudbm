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

mod gdbm_sys;

use std::ops::Drop;
use std::default::Default;
use std::path::Path;
use std::slice;
use std::ffi::{CString, CStr};
use std::os::unix::ffi::OsStrExt;


use serde::{Serialize, Deserialize};
use serde::de::DeserializeOwned;

pub struct Database {
    handle: gdbm_sys::GDBM_FILE,
}

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

pub struct Entry<'a> {
    datum: gdbm_sys::datum,
    slice: &'a [u8],
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

    pub fn into_type<T>(self) -> Result<T, bincode::Error>
        where T: DeserializeOwned
    {
        bincode::deserialize(self.slice)
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

    pub fn open<P: AsRef<Path>>(&self, path: P) -> Result<Database, String> {
        let path = path.as_ref();
        let handle = self.gdbm_open(&path)?;
        Ok(Database { handle })
    }

    pub fn open_readonly<P: AsRef<Path>>(&mut self, path: P)
        -> Result<ReadOnlyDb, String> {
        self.readonly = true;
        let db = self.open(path)?;
        Ok(ReadOnlyDb(db))
    }

    fn gdbm_open(&self, path: &Path) -> Result<gdbm_sys::GDBM_FILE, String> {
        //TODO: remove the unwrap and return an error if path contains
        //an interior null byte
        let path = CString::new(path.as_os_str().as_bytes())
            .expect("Path should never contain interior null byte?");
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
            Err(get_error())
        } else {
            Ok(handle)
        }
    }
}

impl Database {
    pub fn store<T>(&mut self, key: &[u8], value: &T) -> Result<(), ()>
        where T: ?Sized + Serialize
    {
        let bytes = bincode::serialize(value).map_err(|_|())?;

        let key_d: gdbm_sys::datum = key.into();

        let value_d = gdbm_sys::datum {
            dptr: bytes.as_ptr() as *mut i8,
            dsize: bytes.len() as i32,
        };

        //TODO: support for insertion with replacement
        let result = unsafe {
            gdbm_sys::gdbm_store(self.handle, key_d, value_d, gdbm_sys::GDBM_INSERT as i32)
        };

        //TODO: check result, return some error type if needed
        if result == 0 { Ok(()) } else { Err(()) }
    }

    pub fn fetch(&self, key: &[u8]) -> Result<Entry, ()> {
        let key_d: gdbm_sys::datum = key.into();
        let result = unsafe { gdbm_sys::gdbm_fetch(self.handle, key_d) };

        if result.dptr.is_null() {
            Err(())
        } else {
            Ok(Entry::new(result))
        }
    }

    pub fn delete(&self, key: &[u8]) -> Result<(), ()> {
        let result = unsafe { gdbm_sys::gdbm_delete(self.handle, key.into()) };
        if result == 0 { Ok(()) } else { Err(()) }
    }
}

impl ReadOnlyDb {
    pub fn fetch(&self, key: &[u8]) -> Option<Entry> {
        self.0.fetch(key).ok()
    }
}

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

fn get_error() -> String {
    unsafe {
        let err_loc = gdbm_sys::gdbm_errno_location();
        let error_ptr = gdbm_sys::gdbm_strerror(*err_loc);
        let err_string = CStr::from_ptr(error_ptr);
        return err_string.to_string_lossy().into_owned();
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use tempdir::TempDir;
    use std::thread::sleep;
    use std::time::Duration;
    use std::fs;
    use std::path::PathBuf;

    fn create_db(path: &Path) {
        assert!(!path.exists());
        GdbmOpener::new()
            .create_if_needed(true)
            .open(&path)
            .expect("db creation failed");
        assert!(path.exists());
    }

    #[test]
    fn smoke_test() {
        let dir = TempDir::new("rust_gdbm").unwrap();
        let db_path = dir.path().join("create.db");
        let mut db = GdbmOpener::new()
            .create_if_needed(true)
            .open(&db_path)
            .expect("db creation failed");
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

        let mut db = GdbmOpener::new()
            .open_readonly(&db_path)
            .expect("db read failed");

        let mut db2 = GdbmOpener::new()
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
            let mut db = GdbmOpener::new()
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
        let mut db = GdbmOpener::new()
            .overwrite(true)
            .open(&db_path)
            .expect("db new failed");

        let r = db.fetch("write key".as_bytes());
        assert!(r.is_err());
    }
}

