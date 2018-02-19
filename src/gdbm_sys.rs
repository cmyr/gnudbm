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

include!(concat!(env!("OUT_DIR"), "/gdbm_bindings.rs"));

//TODO: impl drop for datum; requires some fiddling with bindgen

impl<'a> From<&'a [u8]> for datum {
    fn from(src: &'a [u8]) -> datum {
        datum {
            dptr: src.as_ptr() as *mut i8,
            dsize: src.len() as i32,
        }
    }
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
