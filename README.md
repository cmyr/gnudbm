# gnudbm

See the [documentation] for details.

This project provides ergonomic and idiomatic Rust bindings to [gdbm],
a lightweight local key/value database. It allows easy storage and retrieval
of any type that implements `Serialize` and `Deserialize`.

## Requirements

By default, this package includes a recent gdbm and builds it as a static lib.
If you would like to link against the system gdbm, ensure it is up to date
(1.14+) and build with the `system-gdbm` feature.

## Usage

First, add the following to your `Cargo.toml`:

```toml
[dependencies]
gnudbm = "0.2.3"
```

And to your crate root:

```rust
extern crate gnudbm;
```

[gdbm]: http://puszcza.gnu.org.ua/software/gdbm
[from source]: https://www.gnu.org.ua/software/gdbm/download.html
[bindgen]: https://github.com/rust-lang-nursery/rust-bindgen
[bindgen requirements]: https://rust-lang-nursery.github.io/rust-bindgen/requirements.html
[documentation]: https://docs.rs/crate/gnudbm/
