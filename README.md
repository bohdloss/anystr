A crate for abstracting the encoding of an owned or referenced string,
using the `widestring` and `ascii` crates under the hood.

It's aimed at situations where you might want to serialize/deserialize a string, or move it around, but
you don't care about its encoding.
Both std and no-std environments are supported.

The following encodings are currently supported:
- ASCII
- UTF-8
- UTF-16
- UTF-32

This crate provides two main types: the `AnyString`, an owned string type, and the `AnyStr` which is a referenced type.

## Iteration example

```rust
use anystr::AnyStr;
use widestring::utf16str;

let any = AnyStr::Utf16(utf16str!("Hello world, but utf-16!"));

fn print_any(str: AnyStr) {
    for ch in str.chars() {
        print!("{ch}");
    }
    println!();
}

print_any(any);
```

## MSRV

This crate will always target the latest version of rust, but it may be compatible
with older versions.

## Notes

With all that being said, this project was made mostly as a small personal project to be used
as a tool in some situation, and is not intended to replace bigger string handling crates.