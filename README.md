# rpkg-config

`rpkg-config` is a standalone library for parsing and getting information from
`pkg-config`'s `pc` files in Rust.

This is not a replacement for the `pkg-config` crate. If you want to detect and
use installed packages with `pkg-config`, you should use that instead.

To use, first create a `PkgConfig` struct with e.g. `PkgConfig::open`. The
`libs` and `libs_private` methods return an iterator over items in the `Libs`
and `Libs.private` keys, respectively.

Currently that's about it, if you need something else you can open an issue at github.
