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

#[cfg(not(feature = "system-gdbm"))]
const GDBM_VERSION: &str = "1.14.1";

fn main() {
    #[cfg(not(feature = "system-gdbm"))]
    {
        use std::path::PathBuf;
        use std::process::Command;
        use std::fs;
        use std::env;

        let crate_root = PathBuf::from(&env::var("CARGO_MANIFEST_DIR").unwrap());
        let out_dir = PathBuf::from(&env::var("OUT_DIR").unwrap());
        let dest = out_dir.join("build");
        if !dest.exists() {
            fs::create_dir(&dest).unwrap();
        }

        let src_dir = crate_root.join("vendor").join(format!("gdbm-{}", GDBM_VERSION));
        if !dest.join("lib").exists() {
            eprintln!("building gdbm, dest = {}", dest.display());
            assert!(
                Command::new(src_dir.join("configure"))
                .arg("--without-readline")
                .arg(&format!("--prefix={}", dest.display()))
                .current_dir(&src_dir)
                .output()
                .unwrap()
                .status.success()
                );

            assert!(
                Command::new("make")
                .current_dir(&src_dir)
                .output()
                .unwrap()
                .status.success()
                );

            assert!(
                Command::new("make")
                .arg("install")
                .current_dir(&src_dir)
                .output()
                .unwrap()
                .status.success()
                );

            // so we don't dirty our source dir
            let _ = Command::new("make")
                .arg("distclean")
                .current_dir(&src_dir)
                .output();

        }
        println!("cargo:rustc-link-lib=static=gdbm");
        println!("cargo:rustc-flags=-L {}", dest.join("lib").display());
    }

    #[cfg(feature = "system-gdbm")]
    {
        println!("cargo:rustc-link-lib=gdbm");
    }
}
