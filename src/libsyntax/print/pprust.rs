// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use abi;
use ast::{FnMutUnboxedClosureKind, FnOnceUnboxedClosureKind};
use ast::{FnUnboxedClosureKind, MethodImplItem, P};
use ast::{RegionTyParamBound, TraitTyParamBound, UnboxedClosureKind};
use ast::{UnboxedFnTyParamBound, RequiredMethod, ProvidedMethod};
use ast;
use ast_util;
use owned_slice::OwnedSlice;
use attr::{AttrMetaMethods, AttributeMethods};
use codemap::{CodeMap, BytePos};
use codemap;
use diagnostic;
use parse::token::{mod, Token, BinOp};
use parse::token::keywords::{mod, Keyword};
use parse::lexer::comments;
use parse;
use print::pp::{Breaks, Consistent, Inconsistent};
use print::pp;

use std::gc::Gc;
use std::io::{IoResult, MemWriter};
use std::io;
use std::mem;

pub enum AnnNode<'a> {
    NodeIdent(&'a ast::Ident),
    NodeName(&'a ast::Name),
    NodeBlock(&'a ast::Block),
    NodeItem(&'a ast::Item),
    NodeExpr(&'a ast::Expr),
    NodePat(&'a ast::Pat),
}

pub trait PpAnn {
    fn pre(&self, _state: &mut State, _node: AnnNode) -> IoResult<()> { Ok(()) }
    fn post(&self, _state: &mut State, _node: AnnNode) -> IoResult<()> { Ok(()) }
}

pub struct NoAnn;

impl PpAnn for NoAnn {}

pub struct CurrentCommentAndLiteral {
    cur_cmnt: uint,
    cur_lit: uint,
}

pub struct State<'a> {
    pub s: pp::Printer,
    cm: Option<&'a CodeMap>,
    comments: Option<Vec<comments::Comment> >,
    literals: Option<Vec<comments::Literal> >,
    cur_cmnt_and_lit: CurrentCommentAndLiteral,
    ann: &'a PpAnn+'a,
    encode_idents_with_hygiene: bool,
}

pub fn rust_printer(writer: Box<io::Writer+'static>) -> State<'static> {
    static NO_ANN: NoAnn = NoAnn;
    rust_printer_annotated(writer, &NO_ANN)
}

pub fn rust_printer_annotated<'a>(writer: Box<io::Writer+'static>,
                                  ann: &'a PpAnn) -> State<'a> {
    State {
        s: pp::mk_printer(writer, default_columns),
        cm: None,
        comments: None,
        literals: None,
        cur_cmnt_and_lit: CurrentCommentAndLiteral {
            cur_cmnt: 0,
            cur_lit: 0
        },
        ann: ann,
        encode_idents_with_hygiene: false,
    }
}

pub static indent_unit: uint = 4u;

pub static default_columns: uint = 78u;

/// Requires you to pass an input filename and reader so that
/// it can scan the input text for comments and literals to
/// copy forward.
pub fn print_crate<'a>(cm: &'a CodeMap,
                       span_diagnostic: &diagnostic::SpanHandler,
                       krate: &ast::Crate,
                       filename: String,
                       input: &mut io::Reader,
                       out: Box<io::Writer+'static>,
                       ann: &'a PpAnn,
                       is_expanded: bool) -> IoResult<()> {
    let mut s = State::new_from_input(cm,
                                      span_diagnostic,
                                      filename,
                                      input,
                                      out,
                                      ann,
                                      is_expanded);
    try!(s.print_mod(&krate.module, krate.attrs.as_slice()));
    try!(s.print_remaining_comments());
    s.eof()
}

impl<'a> State<'a> {
    pub fn new_from_input(cm: &'a CodeMap,
                          span_diagnostic: &diagnostic::SpanHandler,
                          filename: String,
                          input: &mut io::Reader,
                          out: Box<io::Writer+'static>,
                          ann: &'a PpAnn,
                          is_expanded: bool) -> State<'a> {
        let (cmnts, lits) = comments::gather_comments_and_literals(
            span_diagnostic,
            filename,
            input);

        State::new(
            cm,
            out,
            ann,
            Some(cmnts),
            // If the code is post expansion, don't use the table of
            // literals, since it doesn't correspond with the literals
            // in the AST anymore.
            if is_expanded { None } else { Some(lits) })
    }

    pub fn new(cm: &'a CodeMap,
               out: Box<io::Writer+'static>,
               ann: &'a PpAnn,
               comments: Option<Vec<comments::Comment>>,
               literals: Option<Vec<comments::Literal>>) -> State<'a> {
        State {
            s: pp::mk_printer(out, default_columns),
            cm: Some(cm),
            comments: comments,
            literals: literals,
            cur_cmnt_and_lit: CurrentCommentAndLiteral {
                cur_cmnt: 0,
                cur_lit: 0
            },
            ann: ann,
            encode_idents_with_hygiene: false,
        }
    }
}

pub fn to_string(f: |&mut State| -> IoResult<()>) -> String {
    use std::raw::TraitObject;
    let mut s = rust_printer(box MemWriter::new());
    f(&mut s).unwrap();
    s.eof().unwrap();
    unsafe {
        // FIXME(pcwalton): A nasty function to extract the string from an `io::Writer`
        // that we "know" to be a `MemWriter` that works around the lack of checked
        // downcasts.
        let obj: TraitObject = mem::transmute_copy(&s.s.out);
        let wr: Box<MemWriter> = mem::transmute(obj.data);
        let result =
            String::from_utf8(Vec::from_slice(wr.get_ref().as_slice())).unwrap();
        mem::forget(wr);
        result.to_string()
    }
}

// FIXME (Issue #16472): the thing_to_string_impls macro should go away
// after we revise the syntax::ext::quote::ToToken impls to go directly
// to token-trees instead of thing -> string -> token-trees.

macro_rules! thing_to_string_impls {
    ($to_string:ident) => {

pub fn ty_to_string(ty: &ast::Ty) -> String {
    $to_string(|s| s.print_type(ty))
}

pub fn pat_to_string(pat: &ast::Pat) -> String {
    $to_string(|s| s.print_pat(pat))
}

pub fn arm_to_string(arm: &ast::Arm) -> String {
    $to_string(|s| s.print_arm(arm))
}

pub fn expr_to_string(e: &ast::Expr) -> String {
    $to_string(|s| s.print_expr(e))
}

pub fn lifetime_to_string(e: &ast::Lifetime) -> String {
    $to_string(|s| s.print_lifetime(e))
}

pub fn tt_to_string(tt: &ast::TokenTree) -> String {
    $to_string(|s| s.print_tt(tt))
}

pub fn tts_to_string(tts: &[ast::TokenTree]) -> String {
    $to_string(|s| s.print_tts(tts))
}

pub fn stmt_to_string(stmt: &ast::Stmt) -> String {
    $to_string(|s| s.print_stmt(stmt))
}

pub fn item_to_string(i: &ast::Item) -> String {
    $to_string(|s| s.print_item(i))
}

pub fn generics_to_string(generics: &ast::Generics) -> String {
    $to_string(|s| s.print_generics(generics))
}

pub fn ty_method_to_string(p: &ast::TypeMethod) -> String {
    $to_string(|s| s.print_ty_method(p))
}

pub fn method_to_string(p: &ast::Method) -> String {
    $to_string(|s| s.print_method(p))
}

pub fn fn_block_to_string(p: &ast::FnDecl) -> String {
    $to_string(|s| s.print_fn_block_args(p, None))
}

pub fn path_to_string(p: &ast::Path) -> String {
    $to_string(|s| s.print_path(p, false))
}

pub fn ident_to_string(id: &ast::Ident) -> String {
    $to_string(|s| s.print_ident(*id))
}

pub fn fun_to_string(decl: &ast::FnDecl, fn_style: ast::FnStyle, name: ast::Ident,
                  opt_explicit_self: Option<ast::ExplicitSelf_>,
                  generics: &ast::Generics) -> String {
    $to_string(|s| {
        try!(s.print_fn(decl, Some(fn_style), abi::Rust,
                        name, generics, opt_explicit_self, ast::Inherited));
        try!(s.end()); // Close the head box
        s.end() // Close the outer box
    })
}

pub fn block_to_string(blk: &ast::Block) -> String {
    $to_string(|s| {
        // containing cbox, will be closed by print-block at }
        try!(s.cbox_indent());
        // head-ibox, will be closed by print-block after {
        try!(s.ibox());
        s.print_block(blk)
    })
}

pub fn meta_item_to_string(mi: &ast::MetaItem) -> String {
    $to_string(|s| s.print_meta_item(mi))
}

pub fn attribute_to_string(attr: &ast::Attribute) -> String {
    $to_string(|s| s.print_attribute(attr))
}

pub fn lit_to_string(l: &ast::Lit) -> String {
    $to_string(|s| s.print_literal(l))
}

pub fn explicit_self_to_string(explicit_self: ast::ExplicitSelf_) -> String {
    $to_string(|s| s.print_explicit_self(explicit_self, ast::MutImmutable).map(|_| {}))
}

pub fn variant_to_string(var: &ast::Variant) -> String {
    $to_string(|s| s.print_variant(var))
}

pub fn arg_to_string(arg: &ast::Arg) -> String {
    $to_string(|s| s.print_arg(arg))
}

pub fn mac_to_string(arg: &ast::Mac) -> String {
    $to_string(|s| s.print_mac(arg))
}

} }

thing_to_string_impls!(to_string)

// FIXME (Issue #16472): the whole `with_hygiene` mod should go away
// after we revise the syntax::ext::quote::ToToken impls to go directly
// to token-trees instea of thing -> string -> token-trees.

pub mod with_hygiene {
    use abi;
    use ast;
    use std::io::IoResult;

    // This function is the trick that all the rest of the routines
    // hang on.
    pub fn to_string_hyg(f: |&mut super::State| -> IoResult<()>) -> String {
        super::to_string(|s| {
            s.encode_idents_with_hygiene = true;
            f(s)
        })
    }

    thing_to_string_impls!(to_string_hyg)
}

fn needs_parentheses(expr: &ast::Expr) -> bool {
    match expr.node {
        ast::ExprAssign(..) | ast::ExprBinary(..) |
        ast::ExprFnBlock(..) | ast::ExprProc(..) |
        ast::ExprUnboxedFn(..) | ast::ExprAssignOp(..) |
        ast::ExprCast(..) => true,
        _ => false,
    }
}

impl<'a> State<'a> {
    pub fn token(&mut self, t: token::Token) -> IoResult<()> {
        try!(pp::word(&mut self.s, token::to_string(&t).as_slice()));
        Ok(())
    }

    pub fn keyword(&mut self, keyword: keywords::Keyword) -> IoResult<()> {
        let ident = keyword.to_name().ident();
        // FIXME: is second argument important?
        let token = token::IDENT(ident, false);
        try!(self.token(token));
        Ok(())
    }

    pub fn keyword_sp(&mut self, keyword: keywords::Keyword) -> IoResult<()> {
        try!(self.keyword(keyword));
        try!(self.nbsp());
        Ok(())
    }

    pub fn binop(&mut self, binop: BinOp) -> IoResult<()> {
        try!(self.token(token::BINOP(binop)));
        Ok(())
    }

    pub fn binop_sp(&mut self, binop: BinOp) -> IoResult<()> {
        try!(self.binop(binop));
        try!(self.nbsp());
        Ok(())
    }

    pub fn string(&mut self, string: &str) -> IoResult<()> {
        let name = token::intern(string);
        self.token(token::LIT_STR(name))
    }

    // ": "
    pub fn colon_sp(&mut self) -> IoResult<()> {
        try!(self.token(token::COLON));
        try!(self.space());
        Ok(())
    }

    // ", "
    pub fn comma_sp(&mut self) -> IoResult<()> {
        try!(self.token(token::COMMA));
        try!(self.space());
        Ok(())
    }

    // "= "
    pub fn eq_sp(&mut self) -> IoResult<()> {
        try!(self.token(token::EQ));
        try!(self.space());
        Ok(())
    }

    pub fn ast_binop_sp(&mut self, op: ast::BinOp) -> IoResult<()> {
        match op {
            ast::BiMul => try!(self.binop(token::STAR)),
            ast::BiDiv => try!(self.binop(token::SLASH)),
            ast::BiRem => try!(self.binop(token::PERCENT)),
            ast::BiAdd => try!(self.binop(token::PLUS)),
            ast::BiSub => try!(self.binop(token::MINUS)),
            ast::BiShl => try!(self.binop(token::SHL)),
            ast::BiShr => try!(self.binop(token::SHR)),
            ast::BiBitAnd => try!(self.binop(token::AND)),
            ast::BiBitXor => try!(self.binop(token::CARET)),
            ast::BiBitOr => try!(self.binop(token::OR)),

            ast::BiLt => try!(self.token(token::LT)),
            ast::BiLe => try!(self.token(token::LE)),
            ast::BiGe => try!(self.token(token::GE)),
            ast::BiGt => try!(self.token(token::GT)),
            ast::BiEq => try!(self.token(token::EQEQ)),
            ast::BiNe => try!(self.token(token::NE)),
            ast::BiAnd => try!(self.token(token::ANDAND)),
            ast::BiOr => try!(self.token(token::OROR)),
        }
        Ok(())
    }

    pub fn ast_unop(&mut self, op: ast::UnOp) -> IoResult<()> {
        match op {
            ast::UnBox => {
                try!(self.keyword(keywords::Box));
                try!(self.token(token::LPAREN));
                let ident = token::str_to_ident("GC");
                try!(self.token(token::IDENT(ident, false)));
                try!(self.token(token::RPAREN));
                try!(self.space());
            }
            ast::UnUniq => {
                try!(self.keyword(keywords::Box));
                try!(self.token(token::LPAREN));
                try!(self.token(token::RPAREN));
                try!(self.space());
            }
            ast::UnDeref => try!(self.binop(token::STAR)),
            ast::UnNot => try!(self.token(token::NOT)),
            ast::UnNeg => try!(self.binop(token::MINUS)),
        }
        Ok(())
    }

    pub fn ibox(&mut self) -> IoResult<()> {
        pp::ibox(&mut self.s, 0)
    }

    pub fn ibox_indent(&mut self) -> IoResult<()> {
        pp::ibox(&mut self.s, indent_unit)
    }

    pub fn cbox(&mut self) -> IoResult<()> {
        pp::cbox(&mut self.s, 0)
    }

    pub fn cbox_indent(&mut self) -> IoResult<()> {
        pp::cbox(&mut self.s, indent_unit)
    }

    // close ibox or cbox
    pub fn end(&mut self) -> IoResult<()> {
        pp::end(&mut self.s)
    }

    pub fn space(&mut self) -> IoResult<()> {
        if !self.is_bol() { try!(pp::space(&mut self.s)); }
        Ok(())
    }

    pub fn hardbreak(&mut self) -> IoResult<()> {
        pp::hardbreak(&mut self.s)
    }

    pub fn zerobreak(&mut self) -> IoResult<()> {
        pp::zerobreak(&mut self.s)
    }

    pub fn head(&mut self, head_content: |&mut State| -> IoResult<()>) -> IoResult<()> {
        try!(self.cbox_indent());
        try!(head_content(self));
        self.ibox()
    }

    pub fn head_empty(&mut self) -> IoResult<()> {
        self.head(|_| Ok(()))
    }

    pub fn eof(&mut self) -> IoResult<()> {
        pp::eof(&mut self.s)
    }

    pub fn nbsp(&mut self) -> IoResult<()> { pp::word(&mut self.s, " ") }

    pub fn popen(&mut self) -> IoResult<()> { self.token(token::LPAREN) }

    pub fn pclose(&mut self) -> IoResult<()> { self.token(token::RPAREN) }

    pub fn bopen(&mut self) -> IoResult<()> {
        try!(self.token(token::LBRACE));
        self.end() // close the head-box
    }

    pub fn bclose_maybe_open(&mut self, span: codemap::Span, close_box: bool) -> IoResult<()> {
        try!(self.maybe_print_comment(span.hi));
        try!(self.break_unindent());
        try!(self.token(token::RBRACE));
        if close_box {
            try!(self.end()); // close the outer-box
        }
        Ok(())
    }

    pub fn bclose(&mut self, span: codemap::Span) -> IoResult<()> {
        self.bclose_maybe_open(span, true)
    }

    pub fn is_begin(&mut self) -> bool {
        match self.s.last_token() { pp::Begin(_) => true, _ => false }
    }

    pub fn is_end(&mut self) -> bool {
        match self.s.last_token() { pp::End => true, _ => false }
    }

    // is this the beginning of a line?
    pub fn is_bol(&mut self) -> bool {
        self.s.last_token().is_eof() || self.s.last_token().is_hardbreak_tok()
    }

    pub fn hardbreak_if_not_bol(&mut self) -> IoResult<()> {
        if !self.is_bol() {
            try!(self.hardbreak())
        }
        Ok(())
    }

    pub fn break_unindent(&mut self) -> IoResult<()> {
        let off = -(indent_unit as int);
        if !self.is_bol() {
            pp::break_offset(&mut self.s, 1, off)
        } else {
            if self.s.last_token().is_hardbreak_tok() {
                // We do something pretty sketchy here: tuck the nonzero
                // offset-adjustment we were going to deposit along with the
                // break into the previous hardbreak.
                self.s.replace_last_token(pp::hardbreak_tok_offset(off));
            }
            Ok(())
        }
    }

    // Synthesizes a comment that was not textually present in the original source
    // file.
    pub fn synth_comment(&mut self, text: String) -> IoResult<()> {
        try!(pp::word(&mut self.s, "/*"));
        try!(self.space());
        try!(pp::word(&mut self.s, text.as_slice()));
        try!(self.space());
        pp::word(&mut self.s, "*/")
    }

    pub fn commasep<T>(&mut self, b: Breaks, elts: &[T],
                       op: |&mut State, &T| -> IoResult<()>)
        -> IoResult<()> {
        match b {
            Inconsistent => try!(self.ibox()),
            Consistent => try!(self.cbox()),
        }
        let mut first = true;
        for elt in elts.iter() {
            if first { first = false; } else { try!(self.comma_sp()); }
            try!(op(self, elt));
        }
        self.end()
    }


    pub fn commasep_cmnt<T>(&mut self,
                            b: Breaks,
                            elts: &[T],
                            op: |&mut State, &T| -> IoResult<()>,
                            get_span: |&T| -> codemap::Span) -> IoResult<()> {
        match b {
            Inconsistent => try!(self.ibox()),
            Consistent => try!(self.cbox()),
        }
        let len = elts.len();
        let mut i = 0u;
        for elt in elts.iter() {
            try!(self.maybe_print_comment(get_span(elt).hi));
            try!(op(self, elt));
            i += 1u;
            if i < len {
                try!(self.token(token::COMMA));
                try!(self.maybe_print_trailing_comment(get_span(elt),
                                                    Some(get_span(&elts[i]).hi)));
                try!(self.space());
            }
        }
        self.end()
    }

    pub fn commasep_exprs(&mut self, exprs: &[Gc<ast::Expr>]) -> IoResult<()> {
        self.commasep_cmnt(Inconsistent, exprs, |s, e| s.print_expr(&**e), |e| e.span)
    }

    pub fn print_mod(&mut self, _mod: &ast::Mod,
                     attrs: &[ast::Attribute]) -> IoResult<()> {
        try!(self.print_inner_attributes(attrs));
        for vitem in _mod.view_items.iter() {
            try!(self.print_view_item(vitem));
        }
        for item in _mod.items.iter() {
            try!(self.print_item(&**item));
        }
        Ok(())
    }

    pub fn print_foreign_mod(&mut self, nmod: &ast::ForeignMod,
                             attrs: &[ast::Attribute]) -> IoResult<()> {
        try!(self.print_inner_attributes(attrs));
        for vitem in nmod.view_items.iter() {
            try!(self.print_view_item(vitem));
        }
        for item in nmod.items.iter() {
            try!(self.print_foreign_item(&**item));
        }
        Ok(())
    }

    pub fn print_opt_lifetime(&mut self,
                              lifetime: &Option<ast::Lifetime>) -> IoResult<()> {
        for l in lifetime.iter() {
            try!(self.print_lifetime(l));
            try!(self.nbsp());
        }
        Ok(())
    }

    pub fn print_type(&mut self, ty: &ast::Ty) -> IoResult<()> {
        try!(self.maybe_print_comment(ty.span.lo));
        try!(self.ibox());
        match ty.node {
            ast::TyNil => {
                try!(self.token(token::LPAREN));
                try!(self.token(token::RPAREN));
            }
            ast::TyBot => try!(self.token(token::NOT)),
            ast::TyBox(ref ty) => {
                try!(self.token(token::AT));
                try!(self.print_type(&**ty));
            }
            ast::TyUniq(ref ty) => {
                try!(self.token(token::TILDE));
                try!(self.print_type(&**ty));
            }
            ast::TyVec(ref ty) => {
                try!(self.token(token::LBRACKET));
                try!(self.print_type(&**ty));
                try!(self.token(token::RBRACKET));
            }
            ast::TyPtr(ref mt) => {
                try!(self.binop(token::STAR));
                match mt.mutbl {
                    ast::MutMutable => try!(self.keyword_sp(keywords::Mut)),
                    ast::MutImmutable => try!(self.keyword_sp(keywords::Const)),
                }
                try!(self.print_type(&*mt.ty));
            }
            ast::TyRptr(ref lifetime, ref mt) => {
                try!(self.binop(token::AND));
                try!(self.print_opt_lifetime(lifetime));
                try!(self.print_mt(mt));
            }
            ast::TyTup(ref elts) => {
                try!(self.popen());
                try!(self.commasep(Inconsistent, elts.as_slice(), |s, ty| s.print_type_ref(ty)));
                if elts.len() == 1 {
                    try!(self.token(token::COMMA));
                }
                try!(self.pclose());
            }
            ast::TyParen(ref typ) => {
                try!(self.popen());
                try!(self.print_type(&**typ));
                try!(self.pclose());
            }
            ast::TyBareFn(f) => {
                let generics = ast::Generics {
                    lifetimes: f.lifetimes.clone(),
                    ty_params: OwnedSlice::empty(),
                    where_clause: ast::WhereClause {
                        id: ast::DUMMY_NODE_ID,
                        predicates: Vec::new(),
                    },
                };
                try!(self.print_ty_fn(Some(f.abi),
                                      None,
                                      f.fn_style,
                                      ast::Many,
                                      &*f.decl,
                                      None,
                                      &OwnedSlice::empty(),
                                      Some(&generics),
                                      None,
                                      None));
            }
            ast::TyClosure(f) => {
                let generics = ast::Generics {
                    lifetimes: f.lifetimes.clone(),
                    ty_params: OwnedSlice::empty(),
                    where_clause: ast::WhereClause {
                        id: ast::DUMMY_NODE_ID,
                        predicates: Vec::new(),
                    },
                };
                try!(self.print_ty_fn(None,
                                      Some('&'),
                                      f.fn_style,
                                      f.onceness,
                                      &*f.decl,
                                      None,
                                      &f.bounds,
                                      Some(&generics),
                                      None,
                                      None));
            }
            ast::TyProc(ref f) => {
                let generics = ast::Generics {
                    lifetimes: f.lifetimes.clone(),
                    ty_params: OwnedSlice::empty(),
                    where_clause: ast::WhereClause {
                        id: ast::DUMMY_NODE_ID,
                        predicates: Vec::new(),
                    },
                };
                try!(self.print_ty_fn(None,
                                      Some('~'),
                                      f.fn_style,
                                      f.onceness,
                                      &*f.decl,
                                      None,
                                      &f.bounds,
                                      Some(&generics),
                                      None,
                                      None));
            }
            ast::TyUnboxedFn(f) => {
                try!(self.print_ty_fn(None,
                                      None,
                                      ast::NormalFn,
                                      ast::Many,
                                      &*f.decl,
                                      None,
                                      &OwnedSlice::empty(),
                                      None,
                                      None,
                                      Some(f.kind)));
            }
            ast::TyPath(ref path, ref bounds, _) => {
                try!(self.print_bounded_path(path, bounds));
            }
            ast::TyFixedLengthVec(ref ty, ref v) => {
                try!(self.token(token::LBRACKET));
                try!(self.print_type(&**ty));
                try!(self.comma_sp());
                try!(self.token(token::DOTDOT));
                try!(self.print_expr(&**v));
                try!(self.token(token::RBRACKET));
            }
            ast::TyTypeof(ref e) => {
                try!(self.keyword(keywords::Typeof));
                try!(self.token(token::LPAREN));
                try!(self.print_expr(&**e));
                try!(self.token(token::RPAREN));
            }
            ast::TyInfer => {
                try!(self.token(token::UNDERSCORE));
            }
        }
        self.end()
    }

    pub fn print_type_ref(&mut self, ty: &P<ast::Ty>) -> IoResult<()> {
        self.print_type(&**ty)
    }

    pub fn print_foreign_item(&mut self,
                              item: &ast::ForeignItem) -> IoResult<()> {
        try!(self.hardbreak_if_not_bol());
        try!(self.maybe_print_comment(item.span.lo));
        try!(self.print_outer_attributes(item.attrs.as_slice()));
        match item.node {
            ast::ForeignItemFn(ref decl, ref generics) => {
                try!(self.print_fn(&**decl, None, abi::Rust, item.ident, generics,
                                   None, item.vis));
                try!(self.end()); // end head-ibox
                try!(self.token(token::SEMI));
                self.end() // end the outer fn box
            }
            ast::ForeignItemStatic(ref t, m) => {
                try!(self.head(|s| {
                    try!(s.print_visibility(item.vis));
                    try!(s.keyword_sp(keywords::Static));
                    if m {
                        try!(s.keyword_sp(keywords::Mut));
                    }
                    Ok(())
                }));

                try!(self.print_ident(item.ident));
                try!(self.colon_sp());
                try!(self.print_type(&**t));
                try!(self.token(token::SEMI));
                try!(self.end()); // end the head-ibox

                self.end() // end the outer cbox
            }
        }
    }

    /// Pretty-print an item
    pub fn print_item(&mut self, item: &ast::Item) -> IoResult<()> {
        try!(self.hardbreak_if_not_bol());
        try!(self.maybe_print_comment(item.span.lo));
        try!(self.print_outer_attributes(item.attrs.as_slice()));
        try!(self.ann.pre(self, NodeItem(item)));
        match item.node {
            ast::ItemStatic(ref ty, m, ref expr) => {
                try!(self.head(|s| {
                    try!(s.print_visibility(item.vis));
                    try!(s.keyword_sp(keywords::Static));
                    if m == ast::MutMutable {
                        try!(s.keyword_sp(keywords::Mut));
                    }
                    Ok(())
                }));

                try!(self.print_ident(item.ident));
                try!(self.colon_sp());
                try!(self.print_type(&**ty));
                try!(self.space());
                try!(self.end()); // end the head-ibox

                try!(self.token(token::EQ));
                try!(self.space());
                try!(self.print_expr(&**expr));
                try!(self.token(token::SEMI));
                try!(self.end()); // end the outer cbox
            }
            ast::ItemFn(ref decl, fn_style, abi, ref typarams, ref body) => {
                try!(self.print_fn(
                    &**decl,
                    Some(fn_style),
                    abi,
                    item.ident,
                    typarams,
                    None,
                    item.vis
                ));
                try!(self.nbsp());
                try!(self.print_block_with_attrs(&**body, item.attrs.as_slice()));
            }
            ast::ItemMod(ref _mod) => {
                try!(self.head(|s| {
                    try!(s.print_visibility(item.vis));
                    try!(s.keyword_sp(keywords::Mod));
                    Ok(())
                }));
                try!(self.print_ident(item.ident));
                try!(self.nbsp());
                try!(self.bopen());
                try!(self.print_mod(_mod, item.attrs.as_slice()));
                try!(self.bclose(item.span));
            }
            ast::ItemForeignMod(ref nmod) => {
                try!(self.head(|s| {
                    s.keyword_sp(keywords::Extern)
                }));
                try!(self.string(nmod.abi.name()));
                try!(self.bopen());
                try!(self.print_foreign_mod(nmod, item.attrs.as_slice()));
                try!(self.bclose(item.span));
            }
            ast::ItemTy(ref ty, ref params) => {
                try!(self.ibox_indent());

                try!(self.ibox());
                try!(self.print_visibility(item.vis));
                try!(self.keyword_sp(keywords::Type));
                try!(self.print_ident(item.ident));
                try!(self.print_generics(params));
                try!(self.end()); // end the inner ibox

                try!(self.space());
                try!(self.token(token::EQ));
                try!(self.space());
                try!(self.print_type(&**ty));
                try!(self.print_where_clause(params));
                try!(self.token(token::SEMI));
                try!(self.end()); // end the outer ibox
            }
            ast::ItemEnum(ref enum_definition, ref params) => {
                try!(self.print_enum_def(
                    enum_definition,
                    params,
                    item.ident,
                    item.span,
                    item.vis
                ));
            }
            ast::ItemStruct(ref struct_def, ref generics) => {
                try!(self.head(|s| {
                    if struct_def.is_virtual {
                        try!(s.keyword_sp(keywords::Virtual));
                    }
                    try!(s.print_visibility(item.vis));
                    s.keyword_sp(keywords::Struct)
                }));
                try!(self.print_struct(&**struct_def, generics, item.ident,
                                       item.span));
            }

            ast::ItemImpl(ref generics,
                          ref opt_trait,
                          ref ty,
                          ref impl_items) => {
                try!(self.head(|s| {
                    try!(s.print_visibility(item.vis));
                    s.keyword_sp(keywords::Impl)
                }));
                if generics.is_parameterized() {
                    try!(self.print_generics(generics));
                    try!(self.space());
                }

                match opt_trait {
                    &Some(ref t) => {
                        try!(self.print_trait_ref(t));
                        try!(self.space());
                        try!(self.keyword_sp(keywords::For));
                    }
                    &None => {}
                }

                try!(self.print_type(&**ty));
                try!(self.print_where_clause(generics));

                try!(self.space());
                try!(self.bopen());
                try!(self.print_inner_attributes(item.attrs.as_slice()));
                for impl_item in impl_items.iter() {
                    match *impl_item {
                        ast::MethodImplItem(meth) => {
                            try!(self.print_method(&*meth));
                        }
                    }
                }
                try!(self.bclose(item.span));
            }
            ast::ItemTrait(ref generics, ref unbound, ref bounds, ref methods) => {
                try!(self.head(|s| {
                    try!(s.print_visibility(item.vis));
                    s.keyword_sp(keywords::Trait)
                }));
                try!(self.print_ident(item.ident));
                try!(self.print_generics(generics));
                match unbound {
                    &Some(TraitTyParamBound(ref tref)) => {
                        try!(self.space());
                        try!(self.keyword_sp(keywords::For));
                        try!(self.print_trait_ref(tref));
                        try!(self.token(token::QUESTION));
                    }
                    _ => {}
                }
                try!(self.print_bounds(true, bounds));
                try!(self.print_where_clause(generics));
                try!(self.nbsp());
                try!(self.bopen());
                for meth in methods.iter() {
                    try!(self.print_trait_method(meth));
                }
                try!(self.bclose(item.span));
            }
            // I think it's reasonable to hide the context here:
            ast::ItemMac(codemap::Spanned { node: ast::MacInvocTT(ref pth, ref tts, _),
                                            ..}) => {
                try!(self.print_visibility(item.vis));
                try!(self.print_path(pth, false));
                try!(self.token(token::NOT));
                try!(self.nbsp());
                try!(self.print_ident(item.ident));
                try!(self.cbox_indent());
                try!(self.popen());
                try!(self.print_tts(tts.as_slice()));
                try!(self.pclose());
                try!(self.end());
            }
        }
        self.ann.post(self, NodeItem(item))
    }

    fn print_trait_ref(&mut self, t: &ast::TraitRef) -> IoResult<()> {
        self.print_path(&t.path, false)
    }

    pub fn print_enum_def(&mut self, enum_definition: &ast::EnumDef,
                          generics: &ast::Generics, ident: ast::Ident,
                          span: codemap::Span,
                          visibility: ast::Visibility) -> IoResult<()> {
        try!(self.head(|s| {
            try!(s.print_visibility(visibility));
            s.keyword_sp(keywords::Enum)
        }));
        try!(self.print_ident(ident));
        try!(self.print_generics(generics));
        try!(self.print_where_clause(generics));
        try!(self.space());
        self.print_variants(enum_definition.variants.as_slice(), span)
    }

    pub fn print_variants(&mut self,
                          variants: &[P<ast::Variant>],
                          span: codemap::Span) -> IoResult<()> {
        try!(self.bopen());
        for v in variants.iter() {
            try!(self.space());
            try!(self.maybe_print_comment(v.span.lo));
            try!(self.print_outer_attributes(v.node.attrs.as_slice()));
            try!(self.ibox_indent());
            try!(self.print_variant(&**v));
            try!(self.token(token::COMMA));
            try!(self.end());
            try!(self.maybe_print_trailing_comment(v.span, None));
        }
        self.bclose(span)
    }

    pub fn print_visibility(&mut self, vis: ast::Visibility) -> IoResult<()> {
        match vis {
            ast::Public => self.keyword_sp(keywords::Pub),
            ast::Inherited => Ok(())
        }
    }

    pub fn print_struct(&mut self,
                        struct_def: &ast::StructDef,
                        generics: &ast::Generics,
                        ident: ast::Ident,
                        span: codemap::Span) -> IoResult<()> {
        try!(self.print_ident(ident));
        try!(self.print_generics(generics));
        match struct_def.super_struct {
            Some(ref t) => {
                try!(self.colon_sp());
                try!(self.print_type(&**t));
            },
            None => {},
        }
        if ast_util::struct_def_is_tuple_like(struct_def) {
            if !struct_def.fields.is_empty() {
                try!(self.popen());
                try!(self.commasep(
                    Inconsistent, struct_def.fields.as_slice(),
                    |s, field| {
                        match field.node.kind {
                            ast::NamedField(..) => fail!("unexpected named field"),
                            ast::UnnamedField(vis) => {
                                try!(s.print_visibility(vis));
                                try!(s.maybe_print_comment(field.span.lo));
                                s.print_type(&*field.node.ty)
                            }
                        }
                    }
                ));
                try!(self.pclose());
            }
            try!(self.token(token::SEMI));
            try!(self.end());
            self.end() // close the outer-box
        } else {
            try!(self.nbsp());
            try!(self.bopen());
            try!(self.hardbreak_if_not_bol());

            for field in struct_def.fields.iter() {
                match field.node.kind {
                    ast::UnnamedField(..) => fail!("unexpected unnamed field"),
                    ast::NamedField(ident, visibility) => {
                        try!(self.hardbreak_if_not_bol());
                        try!(self.maybe_print_comment(field.span.lo));
                        try!(self.print_outer_attributes(field.node.attrs.as_slice()));
                        try!(self.print_visibility(visibility));
                        try!(self.print_ident(ident));
                        try!(self.token(token::COLON));
                        try!(self.nbsp());
                        try!(self.print_type(&*field.node.ty));
                        try!(self.token(token::COMMA));
                    }
                }
            }

            self.bclose(span)
        }
    }

    /// This doesn't deserve to be called "pretty" printing, but it should be
    /// meaning-preserving. A quick hack that might help would be to look at the
    /// spans embedded in the TTs to decide where to put spaces and newlines.
    /// But it'd be better to parse these according to the grammar of the
    /// appropriate macro, transcribe back into the grammar we just parsed from,
    /// and then pretty-print the resulting AST nodes (so, e.g., we print
    /// expression arguments as expressions). It can be done! I think.
    pub fn print_tt(&mut self, tt: &ast::TokenTree) -> IoResult<()> {
        match *tt {
            ast::TTDelim(ref tts) => self.print_tts(tts.as_slice()),
            ast::TTTok(_, ref tk) => {
                try!(self.token(tk.clone()));
                match *tk {
                    parse::token::DOC_COMMENT(..) => {
                        self.hardbreak()
                    }
                    _ => Ok(())
                }
            }
            ast::TTSeq(_, ref tts, ref sep, zerok) => {
                try!(self.token(token::DOLLAR));
                try!(self.token(token::LPAREN));
                for tt_elt in (*tts).iter() {
                    try!(self.print_tt(tt_elt));
                }
                try!(self.token(token::RPAREN));
                match *sep {
                    Some(ref tk) => {
                        try!(self.token(tk.clone()));
                    }
                    None => ()
                }
                self.binop_sp(if zerok { token::STAR } else { token::PLUS })
            }
            ast::TTNonterminal(_, name) => {
                try!(self.token(token::DOLLAR));
                self.print_ident(name)
            }
        }
    }

    pub fn print_tts(&mut self, tts: &[ast::TokenTree]) -> IoResult<()> {
        try!(self.ibox());
        for (i, tt) in tts.iter().enumerate() {
            if i != 0 {
                try!(self.space());
            }
            try!(self.print_tt(tt));
        }
        self.end()
    }

    pub fn print_variant(&mut self, v: &ast::Variant) -> IoResult<()> {
        try!(self.print_visibility(v.node.vis));
        match v.node.kind {
            ast::TupleVariantKind(ref args) => {
                try!(self.print_ident(v.node.name));
                if !args.is_empty() {
                    try!(self.popen());
                    try!(self.commasep(Consistent,
                                       args.as_slice(),
                                       |s, arg| s.print_type(&*arg.ty)));
                    try!(self.pclose());
                }
            }
            ast::StructVariantKind(ref struct_def) => {
                try!(self.head_empty());
                let generics = ast_util::empty_generics();
                try!(self.print_struct(&**struct_def, &generics, v.node.name, v.span));
            }
        }
        match v.node.disr_expr {
            Some(ref d) => {
                try!(self.space());
                try!(self.token(token::EQ));
                try!(self.space());
                self.print_expr(&**d)
            }
            _ => Ok(())
        }
    }

    pub fn print_ty_method(&mut self, m: &ast::TypeMethod) -> IoResult<()> {
        try!(self.hardbreak_if_not_bol());
        try!(self.maybe_print_comment(m.span.lo));
        try!(self.print_outer_attributes(m.attrs.as_slice()));
        try!(self.print_ty_fn(None,
                              None,
                              m.fn_style,
                              ast::Many,
                              &*m.decl,
                              Some(m.ident),
                              &OwnedSlice::empty(),
                              Some(&m.generics),
                              Some(m.explicit_self.node),
                              None));
        self.token(token::SEMI)
    }

    pub fn print_trait_method(&mut self,
                              m: &ast::TraitItem) -> IoResult<()> {
        match *m {
            RequiredMethod(ref ty_m) => self.print_ty_method(ty_m),
            ProvidedMethod(ref m) => self.print_method(&**m)
        }
    }

    pub fn print_impl_item(&mut self, ii: &ast::ImplItem) -> IoResult<()> {
        match *ii {
            MethodImplItem(ref m) => self.print_method(&**m),
        }
    }

    pub fn print_method(&mut self, meth: &ast::Method) -> IoResult<()> {
        try!(self.hardbreak_if_not_bol());
        try!(self.maybe_print_comment(meth.span.lo));
        try!(self.print_outer_attributes(meth.attrs.as_slice()));
        match meth.node {
            ast::MethDecl(ident,
                          ref generics,
                          abi,
                          ref explicit_self,
                          fn_style,
                          decl,
                          body,
                          vis) => {
                try!(self.print_fn(&*decl,
                                   Some(fn_style),
                                   abi,
                                   ident,
                                   generics,
                                   Some(explicit_self.node),
                                   vis));
                try!(self.nbsp());
                self.print_block_with_attrs(&*body, meth.attrs.as_slice())
            },
            ast::MethMac(codemap::Spanned { node: ast::MacInvocTT(ref pth, ref tts, _),
                                            ..}) => {
                // code copied from ItemMac:
                try!(self.print_path(pth, false));
                try!(self.token(token::NOT));
                try!(self.nbsp());
                try!(self.cbox_indent());
                try!(self.popen());
                try!(self.print_tts(tts.as_slice()));
                try!(self.pclose());
                self.end()
            }
        }
    }

    pub fn print_outer_attributes(&mut self,
                                  attrs: &[ast::Attribute]) -> IoResult<()> {
        let mut count = 0u;
        for attr in attrs.iter() {
            match attr.node.style {
                ast::AttrOuter => {
                    try!(self.print_attribute(attr));
                    count += 1;
                }
                _ => {/* fallthrough */ }
            }
        }
        if count > 0 {
            try!(self.hardbreak_if_not_bol());
        }
        Ok(())
    }

    pub fn print_inner_attributes(&mut self,
                                  attrs: &[ast::Attribute]) -> IoResult<()> {
        let mut count = 0u;
        for attr in attrs.iter() {
            match attr.node.style {
                ast::AttrInner => {
                    try!(self.print_attribute(attr));
                    count += 1;
                }
                _ => {/* fallthrough */ }
            }
        }
        if count > 0 {
            try!(self.hardbreak_if_not_bol());
        }
        Ok(())
    }

    pub fn print_attribute(&mut self, attr: &ast::Attribute) -> IoResult<()> {
        try!(self.hardbreak_if_not_bol());
        try!(self.maybe_print_comment(attr.span.lo));
        if attr.node.is_sugared_doc {
            let name = token::intern(attr.value_str().unwrap().get());
            self.token(token::DOC_COMMENT(name))
        } else {
            try!(self.token(token::POUND));
            match attr.node.style {
                ast::AttrInner => try!(self.token(token::NOT)),
                ast::AttrOuter => {}
            }
            try!(self.token(token::LBRACKET));
            try!(self.print_meta_item(&*attr.meta()));
            self.token(token::RBRACKET)
        }
    }


    pub fn print_stmt(&mut self, st: &ast::Stmt) -> IoResult<()> {
        try!(self.maybe_print_comment(st.span.lo));
        match st.node {
            ast::StmtDecl(ref decl, _) => {
                try!(self.print_decl(&**decl));
            }
            ast::StmtExpr(ref expr, _) => {
                try!(self.space());
                try!(self.print_expr(&**expr));
            }
            ast::StmtSemi(ref expr, _) => {
                try!(self.space());
                try!(self.print_expr(&**expr));
                try!(self.token(token::SEMI));
            }
            ast::StmtMac(ref mac, semi) => {
                try!(self.space());
                try!(self.print_mac(mac));
                if semi {
                    try!(self.token(token::SEMI));
                }
            }
        }
        if parse::classify::stmt_ends_with_semi(st) {
            try!(self.token(token::SEMI));
        }
        self.maybe_print_trailing_comment(st.span, None)
    }

    pub fn print_block(&mut self, blk: &ast::Block) -> IoResult<()> {
        self.print_block_with_attrs(blk, &[])
    }

    pub fn print_block_unclosed(&mut self, blk: &ast::Block) -> IoResult<()> {
        self.print_block_unclosed_indent(blk)
    }

    pub fn print_block_unclosed_indent(&mut self, blk: &ast::Block) -> IoResult<()> {
        self.print_block_maybe_unclosed(blk, &[], false)
    }

    pub fn print_block_with_attrs(&mut self,
                                  blk: &ast::Block,
                                  attrs: &[ast::Attribute]) -> IoResult<()> {
        self.print_block_maybe_unclosed(blk, attrs, true)
    }

    pub fn print_block_maybe_unclosed(&mut self,
                                      blk: &ast::Block,
                                      attrs: &[ast::Attribute],
                                      close_box: bool) -> IoResult<()> {
        match blk.rules {
            ast::UnsafeBlock(..) => try!(self.keyword_sp(keywords::Unsafe)),
            ast::DefaultBlock => ()
        }
        try!(self.maybe_print_comment(blk.span.lo));
        try!(self.ann.pre(self, NodeBlock(blk)));
        try!(self.bopen());

        try!(self.print_inner_attributes(attrs));

        for vi in blk.view_items.iter() {
            try!(self.print_view_item(vi));
        }
        for st in blk.stmts.iter() {
            try!(self.print_stmt(&**st));
        }
        match blk.expr {
            Some(ref expr) => {
                try!(self.space());
                try!(self.print_expr(&**expr));
                try!(self.maybe_print_trailing_comment(expr.span, Some(blk.span.hi)));
            }
            _ => ()
        }
        try!(self.bclose_maybe_open(blk.span, close_box));
        self.ann.post(self, NodeBlock(blk))
    }

    fn print_else(&mut self, els: Option<Gc<ast::Expr>>) -> IoResult<()> {
        match els {
            Some(_else) => {
                match _else.node {
                    // "another else-if"
                    ast::ExprIf(ref i, ref t, e) => {
                        try!(self.cbox_indent());
                        try!(self.ibox());
                        try!(self.nbsp());
                        try!(self.keyword_sp(keywords::Else));
                        try!(self.keyword_sp(keywords::If));
                        try!(self.print_expr(&**i));
                        try!(self.nbsp());
                        try!(self.print_block(&**t));
                        self.print_else(e)
                    }
                    // "final else"
                    ast::ExprBlock(ref b) => {
                        try!(self.cbox_indent());
                        try!(self.ibox());
                        try!(self.nbsp());
                        try!(self.keyword_sp(keywords::Else));
                        self.print_block(&**b)
                    }
                    // BLEAH, constraints would be great here
                    _ => {
                        fail!("print_if saw if with weird alternative");
                    }
                }
            }
            _ => Ok(())
        }
    }

    pub fn print_if(&mut self, test: &ast::Expr, blk: &ast::Block,
                    elseopt: Option<Gc<ast::Expr>>) -> IoResult<()> {
        try!(self.head(|s| {
            s.keyword_sp(keywords::If)
        }));
        try!(self.print_expr(test));
        try!(self.nbsp());
        try!(self.print_block(blk));
        self.print_else(elseopt)
    }

    pub fn print_mac(&mut self, m: &ast::Mac) -> IoResult<()> {
        match m.node {
            // I think it's reasonable to hide the ctxt here:
            ast::MacInvocTT(ref pth, ref tts, _) => {
                try!(self.print_path(pth, false));
                try!(self.token(token::NOT));
                try!(self.popen());
                try!(self.print_tts(tts.as_slice()));
                self.pclose()
            }
        }
    }


    fn print_call_post(&mut self, args: &[Gc<ast::Expr>]) -> IoResult<()> {
        try!(self.popen());
        try!(self.commasep_exprs(args));
        self.pclose()
    }

    pub fn print_expr_maybe_paren(&mut self, expr: &ast::Expr) -> IoResult<()> {
        let needs_par = needs_parentheses(expr);
        if needs_par {
            try!(self.popen());
        }
        try!(self.print_expr(expr));
        if needs_par {
            try!(self.pclose());
        }
        Ok(())
    }

    pub fn print_expr(&mut self, expr: &ast::Expr) -> IoResult<()> {
        try!(self.maybe_print_comment(expr.span.lo));
        try!(self.ibox_indent());
        try!(self.ann.pre(self, NodeExpr(expr)));
        match expr.node {
            ast::ExprBox(ref p, ref e) => {
                try!(self.keyword(keywords::Box));
                try!(self.token(token::LPAREN));
                try!(self.print_expr(&**p));
                try!(self.token(token::RPAREN));
                try!(self.space());
                try!(self.print_expr(&**e));
            }
            ast::ExprVec(ref exprs) => {
                try!(self.ibox_indent());
                try!(self.token(token::LBRACKET));
                try!(self.commasep_exprs(exprs.as_slice()));
                try!(self.token(token::RBRACKET));
                try!(self.end());
            }

            ast::ExprRepeat(ref element, ref count) => {
                try!(self.ibox_indent());
                try!(self.token(token::LBRACKET));
                try!(self.print_expr(&**element));
                try!(self.comma_sp());
                try!(self.token(token::DOTDOT));
                try!(self.print_expr(&**count));
                try!(self.token(token::RBRACKET));
                try!(self.end());
            }

            ast::ExprStruct(ref path, ref fields, wth) => {
                try!(self.print_path(path, true));
                try!(self.token(token::LBRACE));
                try!(self.commasep_cmnt(
                    Consistent,
                    fields.as_slice(),
                    |s, field| {
                        try!(s.ibox_indent());
                        try!(s.print_ident(field.ident.node));
                        try!(s.token(token::COLON));
                        try!(s.space());
                        try!(s.print_expr(&*field.expr));
                        s.end()
                    },
                    |f| f.span));
                match wth {
                    Some(ref expr) => {
                        try!(self.ibox());
                        if !fields.is_empty() {
                            try!(self.comma_sp());
                        }
                        try!(self.token(token::DOTDOT));
                        try!(self.print_expr(&**expr));
                        try!(self.end());
                    }
                    _ => try!(self.comma())
                }

                try!(self.token(token::RBRACE));
            }
            ast::ExprTup(ref exprs) => {
                try!(self.popen());
                try!(self.commasep_exprs(exprs.as_slice()));
                if exprs.len() == 1 {
                    try!(self.token(token::COMMA));
                }
                try!(self.pclose());
            }
            ast::ExprCall(ref func, ref args) => {
                try!(self.print_expr_maybe_paren(&**func));
                try!(self.print_call_post(args.as_slice()));
            }
            ast::ExprMethodCall(ident, ref tys, ref args) => {
                let base_args = args.slice_from(1);
                try!(self.print_expr(&**args.get(0)));
                try!(self.token(token::DOT));
                try!(self.print_ident(ident.node));
                if tys.len() > 0u {
                    try!(self.token(token::MOD_SEP));
                    try!(self.token(token::LT));
                    try!(self.commasep(Inconsistent, tys.as_slice(),
                                       |s, ty| s.print_type_ref(ty)));
                    try!(self.token(token::GT));
                }
                try!(self.print_call_post(base_args));
            }
            ast::ExprBinary(op, ref lhs, ref rhs) => {
                try!(self.print_expr(&**lhs));
                try!(self.space());
                try!(self.ast_binop_sp(op));
                try!(self.space());
                try!(self.print_expr(&**rhs));
            }
            ast::ExprUnary(op, ref expr) => {
                try!(self.ast_unop(op));
                try!(self.print_expr_maybe_paren(&**expr));
            }
            ast::ExprAddrOf(m, ref expr) => {
                try!(self.binop(token::AND));
                try!(self.print_mutability(m));
                try!(self.print_expr_maybe_paren(&**expr));
            }
            ast::ExprLit(ref lit) => try!(self.print_literal(&**lit)),
            ast::ExprCast(ref expr, ref ty) => {
                try!(self.print_expr(&**expr));
                try!(self.space());
                try!(self.keyword_sp(keywords::As));
                try!(self.print_type(&**ty));
            }
            ast::ExprIf(ref test, ref blk, elseopt) => {
                try!(self.print_if(&**test, &**blk, elseopt));
            }
            ast::ExprWhile(ref test, ref blk, opt_ident) => {
                for ident in opt_ident.iter() {
                    try!(self.print_ident(*ident));
                    try!(self.colon_sp());
                }
                try!(self.head(|s| {
                    s.keyword_sp(keywords::While)
                }));
                try!(self.print_expr(&**test));
                try!(self.space());
                try!(self.print_block(&**blk));
            }
            ast::ExprForLoop(ref pat, ref iter, ref blk, opt_ident) => {
                for ident in opt_ident.iter() {
                    try!(self.print_ident(*ident));
                    try!(self.colon_sp());
                }
                try!(self.head(|s| {
                    s.keyword_sp(keywords::For)
                }));
                try!(self.print_pat(&**pat));
                try!(self.space());
                try!(self.keyword_sp(keywords::In));
                try!(self.print_expr(&**iter));
                try!(self.space());
                try!(self.print_block(&**blk));
            }
            ast::ExprLoop(ref blk, opt_ident) => {
                for ident in opt_ident.iter() {
                    try!(self.print_ident(*ident));
                    try!(self.colon_sp());
                }
                try!(self.head(|s| {
                    s.keyword_sp(keywords::Loop)
                }));
                try!(self.print_block(&**blk));
            }
            ast::ExprMatch(ref expr, ref arms) => {
                try!(self.head(|s| {
                    try!(s.keyword_sp(keywords::Match));
                    Ok(())
                }));
                try!(self.print_expr(&**expr));
                try!(self.space());
                try!(self.bopen());
                for arm in arms.iter() {
                    try!(self.print_arm(arm));
                }
                try!(self.bclose(expr.span));
            }
            ast::ExprFnBlock(capture_clause, ref decl, ref body) => {
                try!(self.print_capture_clause(capture_clause));

                // in do/for blocks we don't want to show an empty
                // argument list, but at this point we don't know which
                // we are inside.
                //
                // if !decl.inputs.is_empty() {
                try!(self.print_fn_block_args(&**decl, None));
                try!(self.space());
                // }

                if !body.stmts.is_empty() || !body.expr.is_some() {
                    try!(self.print_block_unclosed(&**body));
                } else {
                    // we extract the block, so as not to create another set of boxes
                    match body.expr.unwrap().node {
                        ast::ExprBlock(blk) => {
                            try!(self.print_block_unclosed(&*blk));
                        }
                        _ => {
                            // this is a bare expression
                            try!(self.print_expr(&*body.expr.unwrap()));
                            try!(self.end()); // need to close a box
                        }
                    }
                }
                // a box will be closed by print_expr, but we didn't want an overall
                // wrapper so we closed the corresponding opening. so create an
                // empty box to satisfy the close.
                try!(self.ibox());
            }
            ast::ExprUnboxedFn(capture_clause, kind, ref decl, ref body) => {
                try!(self.print_capture_clause(capture_clause));

                // in do/for blocks we don't want to show an empty
                // argument list, but at this point we don't know which
                // we are inside.
                //
                // if !decl.inputs.is_empty() {
                try!(self.print_fn_block_args(&**decl, Some(kind)));
                try!(self.space());
                // }

                if !body.stmts.is_empty() || !body.expr.is_some() {
                    try!(self.print_block_unclosed(&**body));
                } else {
                    // we extract the block, so as not to create another set of boxes
                    match body.expr.unwrap().node {
                        ast::ExprBlock(ref blk) => {
                            try!(self.print_block_unclosed(&**blk));
                        }
                        _ => {
                            // this is a bare expression
                            try!(self.print_expr(&*body.expr.unwrap()));
                            try!(self.end()); // need to close a box
                        }
                    }
                }
                // a box will be closed by print_expr, but we didn't want an overall
                // wrapper so we closed the corresponding opening. so create an
                // empty box to satisfy the close.
                try!(self.ibox());
            }
            ast::ExprProc(ref decl, ref body) => {
                // in do/for blocks we don't want to show an empty
                // argument list, but at this point we don't know which
                // we are inside.
                //
                // if !decl.inputs.is_empty() {
                try!(self.print_proc_args(&**decl));
                try!(self.space());
                // }
                assert!(body.stmts.is_empty());
                assert!(body.expr.is_some());
                // we extract the block, so as not to create another set of boxes
                match body.expr.unwrap().node {
                    ast::ExprBlock(ref blk) => {
                        try!(self.print_block_unclosed(&**blk));
                    }
                    _ => {
                        // this is a bare expression
                        try!(self.print_expr(&*body.expr.unwrap()));
                        try!(self.end()); // need to close a box
                    }
                }
                // a box will be closed by print_expr, but we didn't want an overall
                // wrapper so we closed the corresponding opening. so create an
                // empty box to satisfy the close.
                try!(self.ibox());
            }
            ast::ExprBlock(ref blk) => {
                // containing cbox, will be closed by print-block at }
                try!(self.cbox_indent());
                // head-box, will be closed by print-block after {
                try!(self.ibox());
                try!(self.print_block(&**blk));
            }
            ast::ExprAssign(ref lhs, ref rhs) => {
                try!(self.print_expr(&**lhs));
                try!(self.space());
                try!(self.eq_sp());
                try!(self.print_expr(&**rhs));
            }
            ast::ExprAssignOp(op, ref lhs, ref rhs) => {
                try!(self.print_expr(&**lhs));
                try!(self.space());
                try!(self.ast_binop_sp(op));
                try!(self.eq_sp());
                try!(self.print_expr(&**rhs));
            }
            ast::ExprField(ref expr, id, ref tys) => {
                try!(self.print_expr(&**expr));
                try!(self.token(token::DOT));
                try!(self.print_ident(id.node));
                if tys.len() > 0u {
                    try!(self.token(token::MOD_SEP));
                    try!(self.token(token::LT));
                    try!(self.commasep(
                        Inconsistent, tys.as_slice(),
                        |s, ty| s.print_type_ref(ty)));
                    try!(self.token(token::GT));
                }
            }
            ast::ExprTupField(ref expr, id, ref tys) => {
                try!(self.print_expr(&**expr));
                try!(self.token(token::DOT));
                try!(self.print_uint(id.node));
                if tys.len() > 0u {
                    try!(self.token(token::MOD_SEP));
                    try!(self.token(token::LT));
                    try!(self.commasep(
                        Inconsistent, tys.as_slice(),
                        |s, ty| s.print_type_ref(ty)));
                    try!(self.token(token::GT));
                }
            }
            ast::ExprIndex(ref expr, ref index) => {
                try!(self.print_expr(&**expr));
                try!(self.token(token::LBRACKET));
                try!(self.print_expr(&**index));
                try!(self.token(token::RBRACKET));
            }
            ast::ExprPath(ref path) => try!(self.print_path(path, true)),
            ast::ExprBreak(opt_ident) => {
                try!(self.keyword(keywords::Break));
                for ident in opt_ident.iter() {
                    try!(self.print_ident(*ident));
                    try!(self.space());
                }
            }
            ast::ExprAgain(opt_ident) => {
                try!(self.keyword(keywords::Continue));
                for ident in opt_ident.iter() {
                    try!(self.print_ident(*ident));
                    try!(self.space())
                }
            }
            ast::ExprRet(ref result) => {
                try!(self.keyword(keywords::Return));
                match *result {
                    Some(ref expr) => {
                        try!(self.nbsp());
                        try!(self.print_expr(&**expr));
                    }
                    _ => ()
                }
            }
            ast::ExprInlineAsm(ref a) => {
                // "asm!"
                let ident = token::str_to_ident("asm");
                try!(self.token(token::IDENT(ident, false)));
                try!(self.token(token::NOT));

                try!(self.popen());
                try!(self.print_string(a.asm.get(), a.asm_str_style));
                try!(self.colon_sp());

                try!(self.commasep(Inconsistent, a.outputs.as_slice(),
                                   |s, &(ref co, ref o, is_rw)| {
                    match co.get().slice_shift_char() {
                        (Some('='), operand) if is_rw => {
                            try!(s.print_string(format!("+{}", operand).as_slice(),
                                                ast::CookedStr))
                        }
                        _ => try!(s.print_string(co.get(), ast::CookedStr))
                    }
                    try!(s.popen());
                    try!(s.print_expr(&**o));
                    try!(s.pclose());
                    Ok(())
                }));
                try!(self.space());
                try!(self.colon_sp());

                try!(self.commasep(Inconsistent, a.inputs.as_slice(),
                                   |s, &(ref co, ref o)| {
                    try!(s.print_string(co.get(), ast::CookedStr));
                    try!(s.popen());
                    try!(s.print_expr(&**o));
                    try!(s.pclose());
                    Ok(())
                }));
                try!(self.space());
                try!(self.colon_sp());

                try!(self.print_string(a.clobbers.get(), ast::CookedStr));
                try!(self.pclose());
            }
            ast::ExprMac(ref m) => try!(self.print_mac(m)),
            ast::ExprParen(ref e) => {
                try!(self.popen());
                try!(self.print_expr(&**e));
                try!(self.pclose());
            }
        }
        try!(self.ann.post(self, NodeExpr(expr)));
        self.end()
    }

    pub fn print_local_decl(&mut self, loc: &ast::Local) -> IoResult<()> {
        try!(self.print_pat(&*loc.pat));
        match loc.ty.node {
            ast::TyInfer => Ok(()),
            _ => {
                try!(self.colon_sp());
                self.print_type(&*loc.ty)
            }
        }
    }

    pub fn print_decl(&mut self, decl: &ast::Decl) -> IoResult<()> {
        try!(self.maybe_print_comment(decl.span.lo));
        match decl.node {
            ast::DeclLocal(ref loc) => {
                try!(self.space());
                try!(self.ibox_indent());
                try!(self.keyword(keywords::Let));
                try!(self.nbsp());

                try!(self.ibox_indent());
                try!(self.print_local_decl(&**loc));
                try!(self.end());
                match loc.init {
                    Some(ref init) => {
                        try!(self.nbsp());
                        try!(self.eq_sp());
                        try!(self.print_expr(&**init));
                    }
                    _ => {}
                }
                self.end()
            }
            ast::DeclItem(ref item) => self.print_item(&**item)
        }
    }

    pub fn print_ident(&mut self, ident: ast::Ident) -> IoResult<()> {
        if self.encode_idents_with_hygiene {
            let encoded = ident.encode_with_hygiene();
            try!(pp::word(&mut self.s, encoded.as_slice()))
        } else {
            try!(self.token(token::IDENT(ident, false)));
        }
        self.ann.post(self, NodeIdent(&ident))
    }

    pub fn print_uint(&mut self, i: uint) -> IoResult<()> {
        let ident = token::str_to_ident(i.to_string().as_slice());
        self.token(token::IDENT(ident, false))
    }

    pub fn print_name(&mut self, name: ast::Name) -> IoResult<()> {
        try!(self.token(token::IDENT(name.ident(), false)));
        self.ann.post(self, NodeName(&name))
    }

    pub fn print_for_decl(&mut self, loc: &ast::Local,
                          coll: &ast::Expr) -> IoResult<()> {
        try!(self.print_local_decl(loc));
        try!(self.space());
        try!(self.keyword_sp(keywords::In));
        self.print_expr(coll)
    }

    fn print_path_(&mut self,
                   path: &ast::Path,
                   colons_before_params: bool,
                   opt_bounds: &Option<OwnedSlice<ast::TyParamBound>>)
        -> IoResult<()> {
        try!(self.maybe_print_comment(path.span.lo));
        if path.global {
            try!(self.token(token::MOD_SEP));
        }

        let mut first = true;
        for segment in path.segments.iter() {
            if first {
                first = false
            } else {
                try!(self.token(token::MOD_SEP))
            }

            try!(self.print_ident(segment.identifier));

            if !segment.lifetimes.is_empty() || !segment.types.is_empty() {
                if colons_before_params {
                    try!(self.token(token::MOD_SEP))
                }
                try!(self.token(token::LT));

                let mut comma = false;
                for lifetime in segment.lifetimes.iter() {
                    if comma {
                        try!(self.comma_sp())
                    }
                    try!(self.print_lifetime(lifetime));
                    comma = true;
                }

                if !segment.types.is_empty() {
                    if comma {
                        try!(self.comma_sp())
                    }
                    try!(self.commasep(
                        Inconsistent,
                        segment.types.as_slice(),
                        |s, ty| s.print_type_ref(ty)));
                }

                try!(self.token(token::GT))
            }
        }

        match *opt_bounds {
            None => Ok(()),
            Some(ref bounds) => self.print_bounds(false, bounds)
        }
    }

    fn print_path(&mut self, path: &ast::Path,
                  colons_before_params: bool) -> IoResult<()> {
        self.print_path_(path, colons_before_params, &None)
    }

    fn print_bounded_path(&mut self, path: &ast::Path,
                          bounds: &Option<OwnedSlice<ast::TyParamBound>>)
        -> IoResult<()> {
        self.print_path_(path, false, bounds)
    }

    pub fn print_pat(&mut self, pat: &ast::Pat) -> IoResult<()> {
        try!(self.maybe_print_comment(pat.span.lo));
        try!(self.ann.pre(self, NodePat(pat)));
        /* Pat isn't normalized, but the beauty of it
         is that it doesn't matter */
        match pat.node {
            ast::PatWild(ast::PatWildSingle) => try!(self.token(token::UNDERSCORE)),
            ast::PatWild(ast::PatWildMulti) => try!(self.token(token::DOTDOT)),
            ast::PatIdent(binding_mode, ref path1, sub) => {
                match binding_mode {
                    ast::BindByRef(mutbl) => {
                        try!(self.keyword_sp(keywords::Ref));
                        try!(self.print_mutability(mutbl));
                    }
                    ast::BindByValue(ast::MutImmutable) => {}
                    ast::BindByValue(ast::MutMutable) => {
                        try!(self.keyword_sp(keywords::Mut));
                    }
                }
                try!(self.print_ident(path1.node));
                match sub {
                    Some(ref p) => {
                        try!(self.token(token::AT));
                        try!(self.print_pat(&**p));
                    }
                    None => ()
                }
            }
            ast::PatEnum(ref path, ref args_) => {
                try!(self.print_path(path, true));
                match *args_ {
                    None => {
                        try!(self.token(token::LPAREN));
                        try!(self.token(token::DOTDOT));
                        try!(self.token(token::RPAREN));
                    }
                    Some(ref args) => {
                        if !args.is_empty() {
                            try!(self.popen());
                            try!(self.commasep(Inconsistent, args.as_slice(),
                                               |s, p| s.print_pat(&**p)));
                            try!(self.pclose());
                        }
                    }
                }
            }
            ast::PatStruct(ref path, ref fields, etc) => {
                try!(self.print_path(path, true));
                try!(self.nbsp());
                try!(self.token(token::LBRACE));
                try!(self.space());

                try!(self.commasep_cmnt(
                    Consistent, fields.as_slice(),
                    |s, f| {
                        try!(s.cbox_indent());
                        try!(s.print_ident(f.ident));
                        try!(s.token(token::COLON));
                        try!(s.nbsp());
                        try!(s.print_pat(&*f.pat));
                        s.end()
                    },
                    |f| f.pat.span));

                if etc {
                    if fields.len() != 0u { try!(self.comma_sp()); }
                    try!(self.token(token::DOTDOT));
                }

                try!(self.token(token::RBRACE));
            }
            ast::PatTup(ref elts) => {
                try!(self.popen());
                try!(self.commasep(Inconsistent,
                                   elts.as_slice(),
                                   |s, p| s.print_pat(&**p)));
                if elts.len() == 1 {
                    try!(self.comma_sp());
                }
                try!(self.pclose());
            }
            ast::PatBox(ref inner) => {
                try!(self.keyword_sp(keywords::Box));
                try!(self.print_pat(&**inner));
            }
            ast::PatRegion(ref inner) => {
                try!(self.binop(token::AND));
                try!(self.print_pat(&**inner));
            }
            ast::PatLit(ref e) => try!(self.print_expr(&**e)),
            ast::PatRange(ref begin, ref end) => {
                try!(self.print_expr(&**begin));
                try!(self.space());
                try!(self.token(token::DOTDOT));
                try!(self.print_expr(&**end));
            }
            ast::PatVec(ref before, slice, ref after) => {
                try!(self.token(token::LBRACKET));
                try!(self.commasep(Inconsistent,
                                   before.as_slice(),
                                   |s, p| s.print_pat(&**p)));
                for p in slice.iter() {
                    if !before.is_empty() { try!(self.comma_sp()); }
                    try!(self.print_pat(&**p));
                    match **p {
                        ast::Pat { node: ast::PatWild(ast::PatWildMulti), .. } => {
                            // this case is handled by print_pat
                        }
                        _ => try!(self.token(token::DOTDOT)),
                    }
                    if !after.is_empty() { try!(self.comma_sp()); }
                }
                try!(self.commasep(Inconsistent,
                                   after.as_slice(),
                                   |s, p| s.print_pat(&**p)));
                try!(self.token(token::RBRACKET));
            }
            ast::PatMac(ref m) => try!(self.print_mac(m)),
        }
        self.ann.post(self, NodePat(pat))
    }

    fn print_arm(&mut self, arm: &ast::Arm) -> IoResult<()> {
        // I have no idea why this check is necessary, but here it
        // is :(
        if arm.attrs.is_empty() {
            try!(self.space());
        }
        try!(self.cbox_indent());
        try!(self.ibox());
        try!(self.print_outer_attributes(arm.attrs.as_slice()));
        let mut first = true;
        for p in arm.pats.iter() {
            if first {
                first = false;
            } else {
                try!(self.space());
                try!(self.binop_sp(token::OR));
            }
            try!(self.print_pat(&**p));
        }
        try!(self.space());
        match arm.guard {
            Some(ref e) => {
                try!(self.keyword_sp(keywords::If));
                try!(self.print_expr(&**e));
                try!(self.space());
            }
            None => ()
        }
        try!(self.token(token::FAT_ARROW));
        try!(self.space());

        match arm.body.node {
            ast::ExprBlock(ref blk) => {
                // the block will close the pattern's ibox
                try!(self.print_block_unclosed_indent(&**blk));
            }
            _ => {
                try!(self.end()); // close the ibox for the pattern
                try!(self.print_expr(&*arm.body));
                try!(self.token(token::COMMA));
            }
        }
        self.end() // close enclosing cbox
    }

    // Returns whether it printed anything
    fn print_explicit_self(&mut self,
                           explicit_self: ast::ExplicitSelf_,
                           mutbl: ast::Mutability) -> IoResult<bool> {
        try!(self.print_mutability(mutbl));
        match explicit_self {
            ast::SelfStatic => { return Ok(false); }
            ast::SelfValue(_) => {
                try!(self.keyword(keywords::Self));
            }
            ast::SelfRegion(ref lt, m, _) => {
                try!(self.binop(token::AND));
                try!(self.print_opt_lifetime(lt));
                try!(self.print_mutability(m));
                try!(self.keyword(keywords::Self));
            }
            ast::SelfExplicit(ref typ, _) => {
                try!(self.keyword(keywords::Self));
                try!(self.colon_sp());
                try!(self.print_type(&**typ));
            }
        }
        return Ok(true);
    }

    pub fn print_fn(&mut self,
                    decl: &ast::FnDecl,
                    fn_style: Option<ast::FnStyle>,
                    abi: abi::Abi,
                    name: ast::Ident,
                    generics: &ast::Generics,
                    opt_explicit_self: Option<ast::ExplicitSelf_>,
                    vis: ast::Visibility) -> IoResult<()> {
        try!(self.head_empty());
        try!(self.print_fn_header_info(opt_explicit_self, fn_style, abi, vis));
        try!(self.nbsp());
        try!(self.print_ident(name));
        try!(self.print_generics(generics));
        try!(self.print_fn_args_and_ret(decl, opt_explicit_self))
        self.print_where_clause(generics)
    }

    pub fn print_fn_args(&mut self, decl: &ast::FnDecl,
                         opt_explicit_self: Option<ast::ExplicitSelf_>)
        -> IoResult<()> {
        // It is unfortunate to duplicate the commasep logic, but we want the
        // self type and the args all in the same box.
        try!(self.ibox());
        let mut first = true;
        for &explicit_self in opt_explicit_self.iter() {
            let m = match explicit_self {
                ast::SelfStatic => ast::MutImmutable,
                _ => match decl.inputs.get(0).pat.node {
                    ast::PatIdent(ast::BindByValue(m), _, _) => m,
                    _ => ast::MutImmutable
                }
            };
            first = !try!(self.print_explicit_self(explicit_self, m));
        }

        // HACK(eddyb) ignore the separately printed self argument.
        let args = if first {
            decl.inputs.as_slice()
        } else {
            decl.inputs.slice_from(1)
        };

        for arg in args.iter() {
            if first { first = false; } else { try!(self.comma_sp()); }
            try!(self.print_arg(arg));
        }

        self.end()
    }

    pub fn print_fn_args_and_ret(&mut self, decl: &ast::FnDecl,
                                 opt_explicit_self: Option<ast::ExplicitSelf_>)
        -> IoResult<()> {
        try!(self.popen());
        try!(self.print_fn_args(decl, opt_explicit_self));
        if decl.variadic {
            try!(self.comma_sp());
            try!(self.token(token::DOTDOTDOT));
        }
        try!(self.pclose());

        try!(self.maybe_print_comment(decl.output.span.lo));
        match decl.output.node {
            ast::TyNil => Ok(()),
            _ => {
                try!(self.space());
                try!(self.token(token::RARROW));
                try!(self.space());
                self.print_type(&*decl.output)
            }
        }
    }

    pub fn print_fn_block_args(
            &mut self,
            decl: &ast::FnDecl,
            unboxed_closure_kind: Option<UnboxedClosureKind>)
            -> IoResult<()> {
        try!(self.binop(token::OR));

        match unboxed_closure_kind {
            None => {}
            Some(FnUnboxedClosureKind) => {
                try!(self.binop(token::AND));
                try!(self.colon_sp());
            }
            Some(FnMutUnboxedClosureKind) => {
                try!(self.binop(token::AND));
                try!(self.keyword_sp(keywords::Mut));
                try!(self.colon_sp());
            }
            Some(FnOnceUnboxedClosureKind) => {
                try!(self.colon_sp());
            }
        }

        try!(self.print_fn_args(decl, None));
        try!(self.binop(token::OR));

        match decl.output.node {
            ast::TyInfer => {}
            _ => {
                try!(self.space());
                try!(self.token(token::RARROW));
                try!(self.space());
                try!(self.print_type(&*decl.output));
            }
        }

        self.maybe_print_comment(decl.output.span.lo)
    }

    pub fn print_capture_clause(&mut self, capture_clause: ast::CaptureClause)
                                -> IoResult<()> {
        match capture_clause {
            ast::CaptureByValue => Ok(()),
            ast::CaptureByRef => self.keyword_sp(keywords::Ref),
        }
    }

    pub fn print_proc_args(&mut self, decl: &ast::FnDecl) -> IoResult<()> {
        try!(self.keyword(keywords::Proc));
        try!(self.token(token::LPAREN));
        try!(self.print_fn_args(decl, None));
        try!(self.token(token::RPAREN));

        match decl.output.node {
            ast::TyInfer => {}
            _ => {
                try!(self.space());
                try!(self.token(token::RARROW));
                try!(self.space());
                try!(self.print_type(&*decl.output));
            }
        }

        self.maybe_print_comment(decl.output.span.lo)
    }

    pub fn print_bounds(&mut self,
                        first_bound: bool,
                        bounds: &OwnedSlice<ast::TyParamBound>)
                        -> IoResult<()> {
        if !bounds.is_empty() {
            if first_bound {
                try!(self.token(token::COLON));
            } else {
                try!(self.binop(token::PLUS));
            }
            let mut first = true;
            for bound in bounds.iter() {
                try!(self.nbsp());
                if first {
                    first = false;
                } else {
                    try!(self.binop_sp(token::PLUS));
                }

                try!(match *bound {
                    TraitTyParamBound(ref tref) => {
                        self.print_trait_ref(tref)
                    }
                    RegionTyParamBound(ref lt) => {
                        self.print_lifetime(lt)
                    }
                    UnboxedFnTyParamBound(ref unboxed_function_type) => {
                        self.print_ty_fn(None,
                                         None,
                                         ast::NormalFn,
                                         ast::Many,
                                         &*unboxed_function_type.decl,
                                         None,
                                         &OwnedSlice::empty(),
                                         None,
                                         None,
                                         Some(unboxed_function_type.kind))
                    }
                })
            }
            Ok(())
        } else {
            Ok(())
        }
    }

    pub fn print_lifetime(&mut self,
                          lifetime: &ast::Lifetime)
                          -> IoResult<()>
    {
        self.print_name(lifetime.name)
    }

    pub fn print_lifetime_def(&mut self,
                              lifetime: &ast::LifetimeDef)
                              -> IoResult<()>
    {
        try!(self.print_lifetime(&lifetime.lifetime));
        let mut first = true;
        for v in lifetime.bounds.iter() {
            if first {
                try!(self.token(token::COLON));
            } else {
                try!(self.binop(token::PLUS));
            }
            try!(self.print_lifetime(v));
            first = false;
        }
        Ok(())
    }

    pub fn print_generics(&mut self,
                          generics: &ast::Generics)
                          -> IoResult<()>
    {
        let total = generics.lifetimes.len() + generics.ty_params.len();
        if total == 0 {
            return Ok(());
        }

        try!(self.token(token::LT));

        let mut ints = Vec::new();
        for i in range(0u, total) {
            ints.push(i);
        }

        try!(self.commasep(Inconsistent, ints.as_slice(), |s, &idx| {
            if idx < generics.lifetimes.len() {
                let lifetime = generics.lifetimes.get(idx);
                s.print_lifetime_def(lifetime)
            } else {
                let idx = idx - generics.lifetimes.len();
                let param = generics.ty_params.get(idx);
                match param.unbound {
                    Some(TraitTyParamBound(ref tref)) => {
                        try!(s.print_trait_ref(tref));
                        try!(s.token(token::QUESTION));
                        try!(s.space());
                    }
                    _ => {}
                }
                try!(s.print_ident(param.ident));
                try!(s.print_bounds(true, &param.bounds));
                match param.default {
                    Some(ref default) => {
                        try!(s.space());
                        try!(s.token(token::EQ));
                        try!(s.space());
                        s.print_type(&**default)
                    }
                    _ => Ok(())
                }
            }
        }));

        try!(self.token(token::GT));
        Ok(())
    }

    pub fn print_where_clause(&mut self, generics: &ast::Generics)
                              -> IoResult<()> {
        if generics.where_clause.predicates.len() == 0 {
            return Ok(())
        }

        try!(self.space());
        try!(self.keyword_sp(keywords::Where));

        for (i, predicate) in generics.where_clause
                                      .predicates
                                      .iter()
                                      .enumerate() {
            if i != 0 {
                try!(self.comma_sp());
            }

            try!(self.print_ident(predicate.ident));
            try!(self.print_bounds(true, &predicate.bounds));
        }

        Ok(())
    }

    pub fn print_meta_item(&mut self, item: &ast::MetaItem) -> IoResult<()> {
        try!(self.ibox_indent());
        match item.node {
            ast::MetaWord(ref name) => {
                let ident = token::str_to_ident(name.get());
                try!(self.token(token::IDENT(ident, false)));
            }
            ast::MetaNameValue(ref name, ref value) => {
                let ident = token::str_to_ident(name.get());
                try!(self.token(token::IDENT(ident, false)));
                try!(self.space());
                try!(self.eq_sp());
                try!(self.print_literal(value));
            }
            ast::MetaList(ref name, ref items) => {
                let ident = token::str_to_ident(name.get());
                try!(self.token(token::IDENT(ident, false)));
                try!(self.popen());
                try!(self.commasep(Consistent,
                                   items.as_slice(),
                                   |s, i| s.print_meta_item(&**i)));
                try!(self.pclose());
            }
        }
        self.end()
    }

    pub fn print_view_path(&mut self, vp: &ast::ViewPath) -> IoResult<()> {
        match vp.node {
            ast::ViewPathSimple(ident, ref path, _) => {
                try!(self.print_path(path, false));

                // FIXME(#6993) can't compare identifiers directly here
                if path.segments.last().unwrap().identifier.name !=
                        ident.name {
                    try!(self.space());
                    try!(self.keyword_sp(keywords::As));
                    try!(self.print_ident(ident));
                }

                Ok(())
            }

            ast::ViewPathGlob(ref path, _) => {
                try!(self.print_path(path, false));
                try!(self.token(token::MOD_SEP));
                try!(self.binop(token::STAR));
                Ok(())
            }

            ast::ViewPathList(ref path, ref idents, _) => {
                if !path.segments.is_empty() {
                    try!(self.print_path(path, false));
                    try!(self.token(token::MOD_SEP));
                }
                try!(self.token(token::LBRACE));
                try!(self.commasep(Inconsistent, idents.as_slice(), |s, w| {
                    match w.node {
                        ast::PathListIdent { name, .. } => {
                            s.print_ident(name)
                        },
                        ast::PathListMod { .. } => {
                            s.keyword(keywords::Mod)
                        }
                    }
                }));
                self.token(token::RBRACE)
            }
        }
    }

    pub fn print_view_item(&mut self, item: &ast::ViewItem) -> IoResult<()> {
        try!(self.hardbreak_if_not_bol());
        try!(self.maybe_print_comment(item.span.lo));
        try!(self.print_outer_attributes(item.attrs.as_slice()));
        try!(self.print_visibility(item.vis));
        match item.node {
            ast::ViewItemExternCrate(id, ref optional_path, _) => {
                try!(self.head(|s| {
                    try!(s.keyword_sp(keywords::Extern));
                    s.keyword_sp(keywords::Crate)
                }));
                for &(ref p, style) in optional_path.iter() {
                    try!(self.print_string(p.get(), style));
                    try!(self.space());
                    try!(self.keyword_sp(keywords::As));
                }
                try!(self.print_ident(id));
            }

            ast::ViewItemUse(ref vp) => {
                try!(self.head(|s| {
                    s.keyword_sp(keywords::Use)
                }));
                try!(self.print_view_path(&**vp));
            }
        }
        try!(self.token(token::SEMI));
        try!(self.end()); // end inner head-block
        self.end() // end outer head-block
    }

    pub fn print_mutability(&mut self,
                            mutbl: ast::Mutability) -> IoResult<()> {
        match mutbl {
            ast::MutMutable => self.keyword_sp(keywords::Mut),
            ast::MutImmutable => Ok(()),
        }
    }

    pub fn print_mt(&mut self, mt: &ast::MutTy) -> IoResult<()> {
        try!(self.print_mutability(mt.mutbl));
        self.print_type(&*mt.ty)
    }

    pub fn print_arg(&mut self, input: &ast::Arg) -> IoResult<()> {
        try!(self.ibox_indent());
        match input.ty.node {
            ast::TyInfer => try!(self.print_pat(&*input.pat)),
            _ => {
                match input.pat.node {
                    ast::PatIdent(_, ref path1, _) if
                        path1.node.name ==
                            parse::token::special_idents::invalid.name => {
                        // Do nothing.
                    }
                    _ => {
                        try!(self.print_pat(&*input.pat));
                        try!(self.colon_sp());
                    }
                }
                try!(self.print_type(&*input.ty));
            }
        }
        self.end()
    }

    pub fn print_ty_fn(&mut self,
                       opt_abi: Option<abi::Abi>,
                       opt_sigil: Option<char>,
                       fn_style: ast::FnStyle,
                       onceness: ast::Onceness,
                       decl: &ast::FnDecl,
                       id: Option<ast::Ident>,
                       bounds: &OwnedSlice<ast::TyParamBound>,
                       generics: Option<&ast::Generics>,
                       opt_explicit_self: Option<ast::ExplicitSelf_>,
                       opt_unboxed_closure_kind:
                        Option<ast::UnboxedClosureKind>)
                       -> IoResult<()> {
        try!(self.ibox_indent());

        // Duplicates the logic in `print_fn_header_info()`.  This is because that
        // function prints the sigil in the wrong place.  That should be fixed.
        if opt_sigil == Some('~') && onceness == ast::Once {
            try!(self.keyword(keywords::Proc));
        } else if opt_sigil == Some('&') {
            try!(self.print_fn_style(fn_style));
            try!(self.print_extern_opt_abi(opt_abi));
            try!(self.print_onceness(onceness));
        } else {
            assert!(opt_sigil.is_none());
            try!(self.print_fn_style(fn_style));
            try!(self.print_opt_abi_and_extern_if_nondefault(opt_abi));
            try!(self.print_onceness(onceness));
            if opt_unboxed_closure_kind.is_none() {
                try!(self.keyword(keywords::Fn));
            }
        }

        match id {
            Some(id) => {
                try!(self.nbsp());
                try!(self.print_ident(id));
            }
            _ => ()
        }

        match generics { Some(g) => try!(self.print_generics(g)), _ => () }
        try!(self.zerobreak());

        if opt_unboxed_closure_kind.is_some() || opt_sigil == Some('&') {
            try!(self.binop(token::OR));
        } else {
            try!(self.popen());
        }

        match opt_unboxed_closure_kind {
            Some(ast::FnUnboxedClosureKind) => {
                try!(self.binop(token::AND));
                try!(self.colon_sp());
            }
            Some(ast::FnMutUnboxedClosureKind) => {
                try!(self.binop(token::AND));
                try!(self.keyword_sp(keywords::Mut));
                try!(self.colon_sp());
            }
            Some(ast::FnOnceUnboxedClosureKind) => {
                try!(self.colon_sp());
            }
            None => {}
        }

        try!(self.print_fn_args(decl, opt_explicit_self));

        if opt_unboxed_closure_kind.is_some() || opt_sigil == Some('&') {
            try!(self.binop(token::OR));
        } else {
            if decl.variadic {
                try!(self.comma_sp());
                try!(self.token(token::DOTDOTDOT));
            }
            try!(self.pclose());
        }

        try!(self.print_bounds(true, bounds));

        try!(self.maybe_print_comment(decl.output.span.lo));

        match decl.output.node {
            ast::TyNil => {}
            _ => {
                try!(self.space());
                try!(self.ibox_indent());
                try!(self.token(token::RARROW));
                try!(self.space());
                if decl.cf == ast::NoReturn {
                    try!(self.token(token::NOT));
                } else {
                    try!(self.print_type(&*decl.output));
                }
                try!(self.end());
            }
        }

        match generics {
            Some(generics) => try!(self.print_where_clause(generics)),
            None => {}
        }

        self.end()
    }

    pub fn maybe_print_trailing_comment(&mut self, span: codemap::Span,
                                        next_pos: Option<BytePos>)
        -> IoResult<()> {
        let cm = match self.cm {
            Some(cm) => cm,
            _ => return Ok(())
        };
        match self.next_comment() {
            Some(ref cmnt) => {
                if (*cmnt).style != comments::Trailing { return Ok(()) }
                let span_line = cm.lookup_char_pos(span.hi);
                let comment_line = cm.lookup_char_pos((*cmnt).pos);
                let mut next = (*cmnt).pos + BytePos(1);
                match next_pos { None => (), Some(p) => next = p }
                if span.hi < (*cmnt).pos && (*cmnt).pos < next &&
                    span_line.line == comment_line.line {
                        try!(self.print_comment(cmnt));
                        self.cur_cmnt_and_lit.cur_cmnt += 1u;
                    }
            }
            _ => ()
        }
        Ok(())
    }

    pub fn print_remaining_comments(&mut self) -> IoResult<()> {
        // If there aren't any remaining comments, then we need to manually
        // make sure there is a line break at the end.
        if self.next_comment().is_none() {
            try!(self.hardbreak());
        }
        loop {
            match self.next_comment() {
                Some(ref cmnt) => {
                    try!(self.print_comment(cmnt));
                    self.cur_cmnt_and_lit.cur_cmnt += 1u;
                }
                _ => break
            }
        }
        Ok(())
    }

    pub fn print_literal(&mut self, lit: &ast::Lit) -> IoResult<()> {
        try!(self.maybe_print_comment(lit.span.lo));
        match self.next_lit(lit.span.lo) {
            Some(ref ltrl) => {
                return pp::word(&mut self.s, (*ltrl).lit.as_slice());
            }
            _ => ()
        }
        match lit.node {
            ast::LitStr(ref st, style) => self.print_string(st.get(), style),
            ast::LitByte(byte) => {
                let mut res = String::new();
                (byte as char).escape_default(|c| res.push_char(c));
                let name = token::intern(res.as_slice());
                self.token(token::LIT_BYTE(name))
            }
            ast::LitChar(ch) => {
                let mut res = String::new();
                ch.escape_default(|c| res.push_char(c));
                let name = token::intern(res.as_slice());
                self.token(token::LIT_CHAR(name))
            }
            ast::LitInt(i, t) => {
                let string = match t {
                    ast::SignedIntLit(st, ast::Plus) => {
                        ast_util::int_ty_to_string(st, Some(i as i64))
                    }
                    ast::SignedIntLit(st, ast::Minus) => {
                        // FIXME: handle overflow?
                        ast_util::int_ty_to_string(st, Some(-(i as i64)))
                    }
                    ast::UnsignedIntLit(ut) => {
                        ast_util::uint_ty_to_string(ut, Some(i))
                    }
                    ast::UnsuffixedIntLit(ast::Plus) => {
                        format!("{}", i)
                    }
                    ast::UnsuffixedIntLit(ast::Minus) => {
                        format!("-{}", i)
                    }
                };
                let name = token::intern(string.as_slice());
                self.token(token::LIT_INTEGER(name))
            }
            ast::LitFloat(ref f, t) => {
                let string = format!("{}{}", f.get(), ast_util::float_ty_to_string(t).as_slice());
                let name = token::intern(string.as_slice());
                self.token(token::LIT_FLOAT(name))
            }
            ast::LitFloatUnsuffixed(ref f) => {
                let name = token::intern(f.get());
                self.token(token::LIT_FLOAT(name))
            }
            ast::LitNil => {
                try!(self.token(token::LPAREN));
                try!(self.token(token::RPAREN));
                Ok(())
            }
            ast::LitBool(val) => {
                let keyword = if val { keywords::True } else { keywords::False };
                self.keyword(keyword)
            }
            ast::LitBinary(ref v) => {
                let string: String = v.iter().map(|&b| b as char).collect();
                let escaped = string.escape_default();
                let name = token::intern(escaped.as_slice());
                self.token(token::LIT_BINARY(name))
            }
        }
    }

    pub fn next_lit(&mut self, pos: BytePos) -> Option<comments::Literal> {
        match self.literals {
            Some(ref lits) => {
                while self.cur_cmnt_and_lit.cur_lit < lits.len() {
                    let ltrl = (*(*lits).get(self.cur_cmnt_and_lit.cur_lit)).clone();
                    if ltrl.pos > pos { return None; }
                    self.cur_cmnt_and_lit.cur_lit += 1u;
                    if ltrl.pos == pos { return Some(ltrl); }
                }
                None
            }
            _ => None
        }
    }

    pub fn maybe_print_comment(&mut self, pos: BytePos) -> IoResult<()> {
        loop {
            match self.next_comment() {
                Some(ref cmnt) => {
                    if (*cmnt).pos < pos {
                        try!(self.print_comment(cmnt));
                        self.cur_cmnt_and_lit.cur_cmnt += 1u;
                    } else { break; }
                }
                _ => break
            }
        }
        Ok(())
    }

    pub fn print_comment(&mut self,
                         cmnt: &comments::Comment) -> IoResult<()> {
        match cmnt.style {
            comments::Mixed => {
                assert_eq!(cmnt.lines.len(), 1u);
                try!(self.zerobreak());
                try!(pp::word(&mut self.s, cmnt.lines.get(0).as_slice()));
                self.zerobreak()
            }
            comments::Isolated => {
                try!(self.hardbreak_if_not_bol());
                for line in cmnt.lines.iter() {
                    // Don't print empty lines because they will end up as trailing
                    // whitespace
                    if !line.is_empty() {
                        try!(pp::word(&mut self.s, line.as_slice()));
                    }
                    try!(self.hardbreak());
                }
                Ok(())
            }
            comments::Trailing => {
                try!(self.nbsp());
                if cmnt.lines.len() == 1u {
                    try!(pp::word(&mut self.s, cmnt.lines.get(0).as_slice()));
                    self.hardbreak()
                } else {
                    try!(self.ibox());
                    for line in cmnt.lines.iter() {
                        if !line.is_empty() {
                            try!(pp::word(&mut self.s, line.as_slice()));
                        }
                        try!(self.hardbreak());
                    }
                    self.end()
                }
            }
            comments::BlankLine => {
                // We need to do at least one, possibly two hardbreaks.
                let is_semi = match self.s.last_token() {
                    pp::String(s, _) => ";" == s.as_slice(),
                    _ => false
                };
                if is_semi || self.is_begin() || self.is_end() {
                    try!(self.hardbreak());
                }
                self.hardbreak()
            }
        }
    }

    pub fn print_string(&mut self, st: &str,
                        style: ast::StrStyle) -> IoResult<()> {
        match style {
            ast::CookedStr => {
                let escaped = st.escape_default();
                self.string(escaped.as_slice())
            }
            ast::RawStr(n) => {
                let name = token::intern(st.as_slice());
                self.token(token::LIT_STR_RAW(name, n))
            }
        }
    }

    pub fn next_comment(&mut self) -> Option<comments::Comment> {
        match self.comments {
            Some(ref cmnts) => {
                if self.cur_cmnt_and_lit.cur_cmnt < cmnts.len() {
                    Some((*cmnts.get(self.cur_cmnt_and_lit.cur_cmnt)).clone())
                } else {
                    None
                }
            }
            _ => None
        }
    }

    pub fn print_opt_fn_style(&mut self,
                            opt_fn_style: Option<ast::FnStyle>) -> IoResult<()> {
        match opt_fn_style {
            Some(fn_style) => self.print_fn_style(fn_style),
            None => Ok(())
        }
    }

    pub fn print_opt_abi_and_extern_if_nondefault(&mut self,
                                                  opt_abi: Option<abi::Abi>)
        -> IoResult<()> {
        match opt_abi {
            Some(abi::Rust) => Ok(()),
            Some(abi) => {
                try!(self.keyword_sp(keywords::Extern));
                try!(self.string(abi.name()));
                self.nbsp()
            }
            None => Ok(())
        }
    }

    pub fn print_extern_opt_abi(&mut self,
                                opt_abi: Option<abi::Abi>) -> IoResult<()> {
        match opt_abi {
            Some(abi) => {
                try!(self.keyword_sp(keywords::Extern));
                try!(self.string(abi.name()));
                self.nbsp()
            }
            None => Ok(())
        }
    }

    pub fn print_fn_header_info(&mut self,
                                _opt_explicit_self: Option<ast::ExplicitSelf_>,
                                opt_fn_style: Option<ast::FnStyle>,
                                abi: abi::Abi,
                                vis: ast::Visibility) -> IoResult<()> {
        try!(self.print_visibility(vis));
        try!(self.print_opt_fn_style(opt_fn_style));

        if abi != abi::Rust {
            try!(self.keyword_sp(keywords::Extern));
            try!(self.string(abi.name()));
            try!(self.nbsp());
        }

        self.keyword(keywords::Fn)
    }

    pub fn print_fn_style(&mut self, s: ast::FnStyle) -> IoResult<()> {
        match s {
            ast::NormalFn => Ok(()),
            ast::UnsafeFn => self.keyword_sp(keywords::Unsafe),
        }
    }

    pub fn print_onceness(&mut self, o: ast::Onceness) -> IoResult<()> {
        match o {
            ast::Once => self.keyword_sp(keywords::Once),
            ast::Many => Ok(())
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use ast;
    use ast_util;
    use codemap;
    use parse::token;

    #[test]
    fn test_fun_to_string() {
        let abba_ident = token::str_to_ident("abba");

        let decl = ast::FnDecl {
            inputs: Vec::new(),
            output: ast::P(ast::Ty {id: 0,
                                    node: ast::TyNil,
                                    span: codemap::DUMMY_SP}),
            cf: ast::Return,
            variadic: false
        };
        let generics = ast_util::empty_generics();
        assert_eq!(&fun_to_string(&decl, ast::NormalFn, abba_ident,
                               None, &generics),
                   &"fn abba()".to_string());
    }

    #[test]
    fn test_variant_to_string() {
        let ident = token::str_to_ident("principal_skinner");

        let var = codemap::respan(codemap::DUMMY_SP, ast::Variant_ {
            name: ident,
            attrs: Vec::new(),
            // making this up as I go.... ?
            kind: ast::TupleVariantKind(Vec::new()),
            id: 0,
            disr_expr: None,
            vis: ast::Public,
        });

        let varstr = variant_to_string(&var);
        assert_eq!(&varstr,&"pub principal_skinner".to_string());
    }
}
