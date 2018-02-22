# gnudbm

This project provides ergonomic and idiomatic Rust bindings to [gdbm],
a lightweight local key/value database. It allows easy storage and retrieval
of any type that implements `Serialize` and `Deserialize`.

## Requirements

- Building uses [bindgen]; see the [bindgen requirements].
- gdbm 1.14. On macOS this is available with `brew
install gdbm`; on other platforms you may need to build [from source].


## Usage

First, add the following to your `Cargo.toml`:

```toml
[dependencies]
gnudbm = "0.1.0"
```

And to your crate root:

```rust
extern crate gnudbm;
```

See the [API documentation] for details.

[gdbm]: http://puszcza.gnu.org.ua/software/gdbm
[from source]: https://www.gnu.org.ua/software/gdbm/download.html
[bindgen]: https://github.com/rust-lang-nursery/rust-bindgen
[bindgen requirements]: https://rust-lang-nursery.github.io/rust-bindgen/requirements.html
[API documentation]: https://docs.rs/crate/gnudbm/
