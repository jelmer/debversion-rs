# debian version handling in rust

This simple crate provides a struct for parsing, validating, manipulating and
comparing Debian version strings.

It aims to follow the version specification as described in Debian policy
5.6.12.

Example:

```rust
use debversion::Version;

let version: Version = "1.0-1".parse()?;
assert_eq!(version.epoch, Some(0));
assert_eq!(version.upstream_version, "1.0");
assert_eq!(version.debian_revision, Some("1"));

let version1: Version = "1.0-0".parse()?;
let version2: Version = "1.0".parse()?;
assert_eq!(version1, version2);

let version1: Version = "1.0-1".parse()?;
let version2: Version = "1.0~alpha1-1".parse()?;
assert!(version2 < version1);
```

## Features

### sqlx

The `sqlx` feature adds serialization support for the postgres
[debversion extension](https://pgxn.org/dist/debversion/) when using sqlx.

### python-debian

The `python-debian` feature provides conversion support between the debversion
Rust type and the ``Version`` class provided by ``python-debian``, when using
[pyo3](https://github.com/pyo3/pyo3).

### serde

The `serde` feature enables serialization to and from simple strings when
using serde.
