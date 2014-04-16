// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


use driver::session::Session;

use syntax::ast;
use syntax::attr;
use syntax::codemap::DUMMY_SP;
use syntax::codemap;
use syntax::fold::Folder;
use syntax::fold;
use syntax::owned_slice::OwnedSlice;
use syntax::parse::token::InternedString;
use syntax::parse::token;
use syntax::util::small_vector::SmallVector;

pub static VERSION: &'static str = "0.11-pre";

pub fn maybe_inject_crates_ref(sess: &Session, krate: ast::Crate)
                               -> ast::Crate {
    if use_std(&krate) {
        inject_crates_ref(sess, krate)
    } else {
        krate
    }
}

pub fn maybe_inject_prelude(sess: &Session, krate: ast::Crate) -> ast::Crate {
    if use_std(&krate) {
        inject_prelude(sess, krate)
    } else {
        krate
    }
}

fn use_std(krate: &ast::Crate) -> bool {
    !attr::contains_name(krate.attrs.as_slice(), "no_std")
}

fn use_start(krate: &ast::Crate) -> bool {
    !attr::contains_name(krate.attrs.as_slice(), "no_start")
}

fn no_prelude(attrs: &[ast::Attribute]) -> bool {
    attr::contains_name(attrs, "no_implicit_prelude")
}

struct StandardLibraryInjector<'a> {
    sess: &'a Session,
}

pub fn with_version(krate: &str) -> Option<(InternedString, ast::StrStyle)> {
    match option_env!("CFG_DISABLE_INJECT_STD_VERSION") {
        Some("1") => None,
        _ => {
            Some((token::intern_and_get_ident(format!("{}\\#{}",
                                                      krate,
                                                      VERSION)),
                  ast::CookedStr))
        }
    }
}

impl<'a> fold::Folder for StandardLibraryInjector<'a> {
    fn fold_crate(&mut self, krate: ast::Crate) -> ast::Crate {
        let mut vis = vec!(ast::ViewItem {
            node: ast::ViewItemExternCrate(token::str_to_ident("std"),
                                         with_version("std"),
                                         ast::DUMMY_NODE_ID),
            attrs: vec!(
                attr::mk_attr(attr::mk_list_item(
                        InternedString::new("phase"),
                        vec!(
                            attr::mk_word_item(InternedString::new("syntax")),
                            attr::mk_word_item(InternedString::new("link")
                        ))))),
            vis: ast::Inherited,
            span: DUMMY_SP
        });

        if use_start(&krate) && !self.sess.building_library.get() {
            vis.push(ast::ViewItem {
                node: ast::ViewItemExternCrate(token::str_to_ident("native"),
                                             with_version("native"),
                                             ast::DUMMY_NODE_ID),
                attrs: Vec::new(),
                vis: ast::Inherited,
                span: DUMMY_SP
            });
        }

        vis.push_all_move(krate.module.view_items.clone());
        let new_module = ast::Mod {
            view_items: vis,
            ..krate.module.clone()
        };

        ast::Crate {
            module: new_module,
            ..krate
        }
    }
}

fn inject_crates_ref(sess: &Session, krate: ast::Crate) -> ast::Crate {
    let mut fold = StandardLibraryInjector {
        sess: sess,
    };
    fold.fold_crate(krate)
}

struct PreludeInjector<'a> {
    sess: &'a Session,
}


impl<'a> fold::Folder for PreludeInjector<'a> {
    fn fold_crate(&mut self, krate: ast::Crate) -> ast::Crate {
        if !no_prelude(krate.attrs.as_slice()) {
            // only add `use std::prelude::*;` if there wasn't a
            // `#![no_implicit_prelude]` at the crate level.
            ast::Crate {
                module: self.fold_mod(&krate.module),
                ..krate
            }
        } else {
            krate
        }
    }

    fn fold_item(&mut self, item: @ast::Item) -> SmallVector<@ast::Item> {
        if !no_prelude(item.attrs.as_slice()) {
            // only recur if there wasn't `#![no_implicit_prelude]`
            // on this item, i.e. this means that the prelude is not
            // implicitly imported though the whole subtree
            fold::noop_fold_item(item, self)
        } else {
            SmallVector::one(item)
        }
    }

    fn fold_mod(&mut self, module: &ast::Mod) -> ast::Mod {
        fn create_path_list(path: &[&str], idents: &[&str]) -> ast::ViewItem {
            let base_path = ast::Path {
                span: DUMMY_SP,
                global: false,
                segments: path.iter().map(|&s| {
                    ast::PathSegment {
                        identifier: token::str_to_ident(s),
                        lifetimes: Vec::new(),
                        types: OwnedSlice::empty(),
                    }
                }).collect(),
            };

            let idents: Vec<ast::PathListIdent> = idents.iter().map(|&s| {
                let ident = ast::PathListIdent_ {
                    name: token::str_to_ident(s),
                    id: ast::DUMMY_NODE_ID,
                };
                codemap::dummy_spanned(ident)
            }).collect();

            let view_path_ = ast::ViewPathList(base_path, idents, ast::DUMMY_NODE_ID);
            let view_path = @codemap::dummy_spanned(view_path_);
            let view_item = ast::ViewItem {
                node: ast::ViewItemUse(vec!(view_path)),
                attrs: Vec::new(),
                vis: ast::Inherited,
                span: DUMMY_SP,
            };
            view_item
        }

        let preludes = [
            // Reexported core operators
            (&["std", "kinds"], &["Copy", "Send", "Sized", "Share"]),
            (&["std", "ops"], &["Add", "Sub", "Mul", "Div", "Rem", "Neg", "Not"]),
            (&["std", "ops"], &["BitAnd", "BitOr", "BitXor"]),
            (&["std", "ops"], &["Drop", "Deref", "DerefMut"]),
            (&["std", "ops"], &["Shl", "Shr", "Index"]),
            (&["std", "option"], &["Option", "Some", "None"]),
            (&["std", "result"], &["Result", "Ok", "Err"]),

            // Reexported functions
            (&["std", "from_str"], &["from_str"]),
            (&["std", "iter"], &["range"]),
            (&["std", "mem"], &["drop"]),

            // Reexported types and traits
            (&["std", "ascii"], &["Ascii", "AsciiCast", "OwnedAsciiCast", "AsciiStr", "IntoBytes"]),
            (&["std", "c_str"], &["ToCStr"]),
            (&["std", "char"], &["Char"]),
            (&["std", "clone"], &["Clone"]),
            (&["std", "cmp"], &["Eq", "Ord", "TotalEq", "TotalOrd", "Ordering", "Less", "Equal", "Greater", "Equiv"]),
            (&["std", "container"], &["Container", "Mutable", "Map", "MutableMap", "Set", "MutableSet"]),
            (&["std", "iter"], &["FromIterator", "Extendable"]),
            (&["std", "iter"], &["Iterator", "DoubleEndedIterator", "RandomAccessIterator", "CloneableIterator"]),
            (&["std", "iter"], &["OrdIterator", "MutableDoubleEndedIterator", "ExactSize"]),
            (&["std", "num"], &["Num", "NumCast", "CheckedAdd", "CheckedSub", "CheckedMul"]),
            (&["std", "num"], &["Signed", "Unsigned", "Round"]),
            (&["std", "num"], &["Primitive", "Int", "Float", "ToPrimitive", "FromPrimitive"]),
            (&["std", "path"], &["GenericPath", "Path", "PosixPath", "WindowsPath"]),
            (&["std", "ptr"], &["RawPtr"]),
            (&["std", "io"], &["Buffer", "Writer", "Reader", "Seek"]),
            (&["std", "str"], &["Str", "StrVector", "StrSlice", "OwnedStr", "IntoMaybeOwned"]),
            (&["std", "to_str"], &["ToStr", "IntoStr"]),
            (&["std", "tuple"], &["Tuple1", "Tuple2", "Tuple3", "Tuple4"]),
            (&["std", "tuple"], &["Tuple5", "Tuple6", "Tuple7", "Tuple8"]),
            (&["std", "tuple"], &["Tuple9", "Tuple10", "Tuple11", "Tuple12"]),
            (&["std", "slice"], &["ImmutableEqVector", "ImmutableTotalOrdVector", "ImmutableCloneableVector"]),
            (&["std", "slice"], &["OwnedVector", "OwnedCloneableVector", "OwnedEqVector"]),
            (&["std", "slice"], &["MutableVector", "MutableTotalOrdVector"]),
            (&["std", "slice"], &["Vector", "VectorVector", "CloneableVector", "ImmutableVector"]),
            (&["std", "strbuf"], &["StrBuf"]),
            (&["std", "vec"], &["Vec"]),

            // Reexported runtime types
            (&["std", "comm"], &["sync_channel", "channel", "SyncSender", "Sender", "Receiver"]),
            (&["std", "task"], &["spawn"]),

            // no GC. :p
        ];

        let preludes = preludes.iter().map(|&(base_path, idents)| {
            create_path_list(base_path, idents)
        }).collect();

        let (crates, uses) = module.view_items.partitioned(|x| {
            match x.node {
                ast::ViewItemExternCrate(..) => true,
                _ => false,
            }
        });

        // add preludes after any `extern crate` but before any `use`
        let mut view_items = crates;
        view_items.push_all_move(preludes);
        view_items.push_all_move(uses);

        // FIXME #2543: Bad copy.
        let new_module = ast::Mod {
            view_items: vis,
            ..(*module).clone()
        };
        fold::noop_fold_mod(&new_module, self)
    }
}

fn inject_prelude(sess: &Session, krate: ast::Crate) -> ast::Crate {
    let mut fold = PreludeInjector {
        sess: sess,
    };
    fold.fold_crate(krate)
}
