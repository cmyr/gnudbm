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

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(dead_code)]


use libc::{c_uint, c_int, c_char, c_ulonglong};

// Open options
pub const GDBM_READER: c_uint = 0;
pub const GDBM_WRITER: c_uint = 1;
pub const GDBM_WRCREAT: c_uint = 2;
pub const GDBM_NEWDB: c_uint = 3;
pub const GDBM_OPENMASK: c_uint = 7;
pub const GDBM_FAST: c_uint = 16;
pub const GDBM_SYNC: c_uint = 32;
pub const GDBM_NOLOCK: c_uint = 64;
pub const GDBM_NOMMAP: c_uint = 128;
pub const GDBM_CLOEXEC: c_uint = 256;
pub const GDBM_BSEXACT: c_uint = 512;
pub const GDBM_CLOERROR: c_uint = 1024;

// Insert options
pub const GDBM_INSERT: c_uint = 0;
pub const GDBM_REPLACE: c_uint = 1;

// Setopt options
pub const GDBM_SETCACHESIZE: c_uint = 1;
pub const GDBM_FASTMODE: c_uint = 2;
pub const GDBM_SETSYNCMODE: c_uint = 3;
pub const GDBM_SETCENTFREE: c_uint = 4;
pub const GDBM_SETCOALESCEBLKS: c_uint = 5;
pub const GDBM_SETMAXMAPSIZE: c_uint = 6;
pub const GDBM_SETMMAP: c_uint = 7;
pub const GDBM_CACHESIZE: c_uint = 1;
pub const GDBM_SYNCMODE: c_uint = 3;
pub const GDBM_CENTFREE: c_uint = 4;
pub const GDBM_COALESCEBLKS: c_uint = 5;
pub const GDBM_GETFLAGS: c_uint = 8;
pub const GDBM_GETMMAP: c_uint = 9;
pub const GDBM_GETCACHESIZE: c_uint = 10;
pub const GDBM_GETSYNCMODE: c_uint = 11;
pub const GDBM_GETCENTFREE: c_uint = 12;
pub const GDBM_GETCOALESCEBLKS: c_uint = 13;
pub const GDBM_GETMAXMAPSIZE: c_uint = 14;
pub const GDBM_GETDBNAME: c_uint = 15;
pub const GDBM_GETBLOCKSIZE: c_uint = 16;

pub const GDBM_VERSION_MAJOR: c_uint = 1;
pub const GDBM_VERSION_MINOR: c_uint = 14;
pub const GDBM_VERSION_PATCH: c_uint = 1;

pub const GDBM_RCVR_DEFAULT: c_uint = 0;
pub const GDBM_RCVR_ERRFUN: c_uint = 1;
pub const GDBM_RCVR_MAX_FAILED_KEYS: c_uint = 2;
pub const GDBM_RCVR_MAX_FAILED_BUCKETS: c_uint = 4;
pub const GDBM_RCVR_MAX_FAILURES: c_uint = 8;
pub const GDBM_RCVR_BACKUP: c_uint = 16;
pub const GDBM_RCVR_FORCE: c_uint = 32;
pub const GDBM_DUMP_FMT_BINARY: c_uint = 0;
pub const GDBM_DUMP_FMT_ASCII: c_uint = 1;
pub const GDBM_META_MASK_MODE: c_uint = 1;
pub const GDBM_META_MASK_OWNER: c_uint = 2;

// Error codes
pub const GDBM_NO_ERROR: c_uint = 0;
pub const GDBM_MALLOC_ERROR: c_uint = 1;
pub const GDBM_BLOCK_SIZE_ERROR: c_uint = 2;
pub const GDBM_FILE_OPEN_ERROR: c_uint = 3;
pub const GDBM_FILE_WRITE_ERROR: c_uint = 4;
pub const GDBM_FILE_SEEK_ERROR: c_uint = 5;
pub const GDBM_FILE_READ_ERROR: c_uint = 6;
pub const GDBM_BAD_MAGIC_NUMBER: c_uint = 7;
pub const GDBM_EMPTY_DATABASE: c_uint = 8;
pub const GDBM_CANT_BE_READER: c_uint = 9;
pub const GDBM_CANT_BE_WRITER: c_uint = 10;
pub const GDBM_READER_CANT_DELETE: c_uint = 11;
pub const GDBM_READER_CANT_STORE: c_uint = 12;
pub const GDBM_READER_CANT_REORGANIZE: c_uint = 13;
pub const GDBM_UNKNOWN_ERROR: c_uint = 14;
pub const GDBM_ITEM_NOT_FOUND: c_uint = 15;
pub const GDBM_REORGANIZE_FAILED: c_uint = 16;
pub const GDBM_CANNOT_REPLACE: c_uint = 17;
pub const GDBM_ILLEGAL_DATA: c_uint = 18;
pub const GDBM_OPT_ALREADY_SET: c_uint = 19;
pub const GDBM_OPT_ILLEGAL: c_uint = 20;
pub const GDBM_BYTE_SWAPPED: c_uint = 21;
pub const GDBM_BAD_FILE_OFFSET: c_uint = 22;
pub const GDBM_BAD_OPEN_FLAGS: c_uint = 23;
pub const GDBM_FILE_STAT_ERROR: c_uint = 24;
pub const GDBM_FILE_EOF: c_uint = 25;
pub const GDBM_NO_DBNAME: c_uint = 26;
pub const GDBM_ERR_FILE_OWNER: c_uint = 27;
pub const GDBM_ERR_FILE_MODE: c_uint = 28;
pub const GDBM_NEED_RECOVERY: c_uint = 29;
pub const GDBM_BACKUP_FAILED: c_uint = 30;
pub const GDBM_DIR_OVERFLOW: c_uint = 31;

pub const _GDBM_MIN_ERRNO: c_uint = 0;
pub const _GDBM_MAX_ERRNO: c_uint = 31;
pub const GDBM_UNKNOWN_UPDATE: c_uint = 14;

#[repr(C)]
#[derive(Debug, Copy)]
pub struct datum {
    pub dptr: *mut c_char,
    pub dsize: c_int,
}

impl Clone for datum {
    fn clone(&self) -> Self { *self }
}

impl<'a> From<&'a [u8]> for datum {
    fn from(src: &'a [u8]) -> datum {
        datum {
            dptr: src.as_ptr() as *mut i8,
            dsize: src.len() as i32,
        }
    }
}


#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct gdbm_file_info { private: [u8; 0] }
pub type GDBM_FILE = *mut gdbm_file_info;

extern "C" {
    pub fn gdbm_fd_open(fd: c_int,
                        file_name: *const c_char,
                        block_size: c_int,
                        flags: c_int,
                        fatal_func: Option<unsafe extern "C" fn(arg1: *const c_char)>)
        -> GDBM_FILE;

    pub fn gdbm_open(arg1: *const c_char,
                     arg2: c_int, arg3: c_int,
                     arg4: c_int,
                     arg5: Option<unsafe extern "C" fn(arg1: *const c_char)>)
        -> GDBM_FILE;

    pub fn gdbm_close(handle: GDBM_FILE);

    pub fn gdbm_store(handle: GDBM_FILE, key: datum, value: datum,
                      flag: c_int) -> c_int;

    pub fn gdbm_fetch(handle: GDBM_FILE, key: datum) -> datum;

    pub fn gdbm_delete(handle: GDBM_FILE, key: datum) -> c_int;

    pub fn gdbm_firstkey(handle: GDBM_FILE) -> datum;

    pub fn gdbm_nextkey(handle: GDBM_FILE, key: datum) -> datum;

    pub fn gdbm_reorganize(handle: GDBM_FILE) -> c_int;

    pub fn gdbm_sync(handle: GDBM_FILE);

    pub fn gdbm_exists(handle: GDBM_FILE, key: datum) -> c_int;

    pub fn gdbm_setopt(handle: GDBM_FILE, arg2: c_int,
                       arg3: *mut ::std::os::raw::c_void,
                       arg4: c_int) -> c_int;

    pub fn gdbm_fdesc(handle: GDBM_FILE) -> c_int;

    pub fn gdbm_export(handle: GDBM_FILE, arg2: *const c_char,
                       arg3: c_int,
                       arg4: c_int) -> c_int;

    pub fn gdbm_errno_location() -> *mut c_int;
    pub fn gdbm_strerror(arg1: c_int) -> *const c_char;
    //pub fn gdbm_export_to_file(dbf: GDBM_FILE, fp: *mut FILE)
     //-> ::std::os::raw::c_int;

    //pub fn gdbm_import(arg1: GDBM_FILE, arg2: *const ::std::os::raw::c_char,
                       //arg3: ::std::os::raw::c_int) -> ::std::os::raw::c_int;

    //pub fn gdbm_import_from_file(dbf: GDBM_FILE, fp: *mut FILE,
                                 //flag: ::std::os::raw::c_int)
     //-> ::std::os::raw::c_int;

    pub fn gdbm_count(dbf: GDBM_FILE, pcount: *mut c_ulonglong)
     -> ::std::os::raw::c_int;
}

#[cfg(test)]
mod test_bindings {
    use super::*;
    use tempdir::TempDir;
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;

    #[test]
    fn multi_reader() {
        let dir = TempDir::new("gdbm_sys").unwrap();
        let db_path = dir.path().join("test.db");
        let path = CString::new(db_path.as_os_str().as_bytes()).unwrap();
        let path_ptr = path.as_ptr() as *mut i8;

        // create db
        let r = unsafe { gdbm_open(path_ptr, 512, GDBM_WRCREAT as i32, 0o666, None) };
        assert!(!r.is_null());

        unsafe { gdbm_close(r) };

        // try to read db:
        let r = unsafe { gdbm_open(path_ptr, 512, GDBM_READER as i32, 0o666, None) };
        assert!(!r.is_null());

        let r1 = unsafe { gdbm_open(path_ptr, 512, GDBM_READER as i32, 0o666, None) };
        assert!(!r1.is_null());
    }
}
