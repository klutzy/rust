// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use extra::hex::ToHex;
use rustc::util::sha2::{Digest, Sha256};

/// Path-fragment identifier of a package such as
/// 'github.com/graydon/test'; path must be a relative
/// path with >=1 component.
#[deriving(Clone, Eq)]
pub struct CrateId {
    /// This is a path, on the local filesystem, referring to where the
    /// files for this package live. For example:
    /// github.com/mozilla/quux-whatever (it's assumed that if we're
    /// working with a package ID of this form, rustpkg has already cloned
    /// the sources into a local directory in the RUST_PATH).
    path: ~str,
    /// Short name. This is the path's filestem, but we store it
    /// redundantly so as to not call get() everywhere (filestem() returns an
    /// option)
    /// The short name does not need to be a valid Rust identifier.
    /// Users can write: `extern mod foo = "...";` to get around the issue
    /// of package IDs whose short names aren't valid Rust identifiers.
    name: ~str,
    /// The requested package version.
    version: Option<~str>
}

impl ToStr for CrateId {
    fn to_str(&self) -> ~str {
        let version = match self.version {
            None => "0.0",
            Some(ref version) => version.as_slice(),
        };
        if self.path == self.name || self.path.ends_with(format!("/{}", self.name)) {
            format!("{}\\#{}", self.path, version)
        } else {
            format!("{}\\#{}:{}", self.path, self.name, version)
        }
    }
}

impl FromStr for CrateId {
    fn from_str(s: &str) -> Option<CrateId> {
        let pieces: ~[&str] = s.splitn('#', 1).collect();
        let path = pieces[0].to_owned();

        if path.starts_with("/") || path.ends_with("/") ||
            path.starts_with(".") || path.is_empty() {
            return None;
        }

        let path_pieces: ~[&str] = path.rsplitn('/', 1).collect();
        let inferred_name = path_pieces[0];

        let (name, version) = if pieces.len() == 1 {
            (inferred_name.to_owned(), None)
        } else {
            let hash_pieces: ~[&str] = pieces[1].splitn(':', 1).collect();
            let (hash_name, hash_version) = if hash_pieces.len() == 1 {
                ("", hash_pieces[0])
            } else {
                (hash_pieces[0], hash_pieces[1])
            };

            let name = if !hash_name.is_empty() {
                hash_name.to_owned()
            } else {
                inferred_name.to_owned()
            };

            let version = if !hash_version.is_empty() {
                Some(hash_version.to_owned())
            } else {
                None
            };

            (name, version)
        };

        Some(CrateId {
            path: path,
            name: name,
            version: version,
        })
    }
}

impl CrateId {
    pub fn version_or_default<'a>(&'a self) -> &'a str {
        match self.version {
            Some(ref ver) => ver.as_slice(),
            None => "0.0"
        }
    }

    pub fn to_lib_name(&self) -> ~str {
        format!("{}-{}-{}", self.name, self.hash(), self.version_or_default())
    }

    pub fn hash(&self) -> ~str {
        let mut hasher = Sha256::new();
        hasher.reset();
        hasher.input_str(self.to_str());
        let hash = hasher.result_bytes().to_hex();
        hash.slice_chars(0, 8).to_owned()
    }

    pub fn short_name_with_version(&self) -> ~str {
        format!("{}-{}", self.name, self.version_or_default())
    }
}
