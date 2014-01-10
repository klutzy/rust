// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use version::split_version;
use extra::hex::ToHex;
use rustc::util::sha2::{Digest, Sha256};

/// Path-fragment identifier of a package such as
/// 'github.com/graydon/test'; path must be a relative
/// path with >=1 component.
#[deriving(Clone)]
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

impl Eq for CrateId {
    fn eq(&self, other: &CrateId) -> bool {
        self.path == other.path && self.version == other.version
    }
}

impl CrateId {
    pub fn version_or_default<'a>(&'a self) -> &'a str {
        match self.version {
            Some(ref ver) => ver.as_slice(),
            None => "0.0"
        }
    }

    pub fn new(s: &str) -> CrateId {
        use conditions::bad_pkg_id::cond;

        // Did the user request a specific version?
        let (s, version) = match split_version(s) {
            Some((path, v)) => {
                (path, v)
            }
            None => {
                (s, None)
            }
        };

        let path = Path::new(s);
        if !path.is_relative() {
            return cond.raise((path, ~"absolute crate_id"));
        }
        if path.filename().is_none() {
            return cond.raise((path, ~"0-length crate_id"));
        }
        let name = path.filestem_str().expect(format!("Strange path! {}", s));

        CrateId {
            path: s.to_owned(),
            name: name.to_owned(),
            version: version
        }
    }

    pub fn to_crate_id_str(&self) -> ~str {
        format!("{}\\#{}", self.path, self.version_or_default())
    }

    pub fn to_lib_name(&self) -> ~str {
        format!("{}-{}-{}", self.name, self.hash(), self.version_or_default())
    }

    pub fn hash(&self) -> ~str {
        let mut hasher = Sha256::new();
        hasher.reset();
        hasher.input_str(self.to_crate_id_str());
        let hash = hasher.result_bytes().to_hex();
        hash.slice_chars(0, 8).to_owned()
    }

    pub fn short_name_with_version(&self) -> ~str {
        format!("{}-{}", self.name, self.version_or_default())
    }

    /// True if the ID has multiple components
    pub fn is_complex(&self) -> bool {
        self.name != self.path
    }

    pub fn prefixes(&self) -> Prefixes {
        prefixes(&Path::new(self.path.as_slice()))
    }

    // This is the workcache function name for the *installed*
    // binaries for this package (as opposed to the built ones,
    // which are per-crate).
    pub fn install_tag(&self) -> ~str {
        format!("install({})", self.to_str())
    }
}

pub fn prefixes(p: &Path) -> Prefixes {
    Prefixes {
        components: p.str_components().map(|x|x.unwrap().to_owned()).to_owned_vec(),
        remaining: ~[]
    }
}

struct Prefixes {
    priv components: ~[~str],
    priv remaining: ~[~str]
}

impl Iterator<(Path, Path)> for Prefixes {
    #[inline]
    fn next(&mut self) -> Option<(Path, Path)> {
        if self.components.len() <= 1 {
            None
        }
        else {
            let last = self.components.pop();
            self.remaining.unshift(last);
            // converting to str and then back is a little unfortunate
            Some((Path::new(self.components.connect("/")),
                  Path::new(self.remaining.connect("/"))))
        }
    }
}

impl ToStr for CrateId {
    fn to_str(&self) -> ~str {
        // should probably use the filestem and not the whole path
        format!("{}-{}", self.path, self.version_or_default())
    }
}

pub fn write<W: Writer>(writer: &mut W, string: &str) {
    writer.write(string.as_bytes());
}
