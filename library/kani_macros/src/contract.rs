// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// Utility functions for macro expansion of function contract clauses.
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use proc_macro2::{Ident, Span};
use quote::{format_ident, quote, ToTokens};
use syn::{
    spanned::Spanned, visit_mut as visitor, Attribute, Expr, ExprCall, FnArg, ItemFn, ReturnType,
    Signature,
};
use uuid::Uuid;

/// Substitution for `old()` expressions.
pub struct OldExpr {
    /// Name of the variable binder.
    pub name: String,
    /// Expression to be evaluated.
    pub expr: Expr,
}

/// Extract calls to the pseudo-function `old()` in post-conditions,
/// which evaluates an expression in a context *before* the
/// to-be-checked-function is executed.
pub fn extract_old_calls(item: &mut ItemFn) -> Vec<OldExpr> {
    struct OldExtractor {
        last_id: usize,
        olds: Vec<OldExpr>,
    }

    // if the call is a call to old() then the argument will be
    // returned.
    fn get_old_data(call: &ExprCall) -> Option<Expr> {
        // must have only one argument
        if call.args.len() != 1 {
            return None;
        }

        if let Expr::Path(path) = &*call.func {
            if path.path.is_ident("old") { Some(call.args[0].clone()) } else { None }
        } else {
            None
        }
    }

    impl visitor::VisitMut for OldExtractor {
        fn visit_expr_mut(&mut self, expr: &mut Expr) {
            if let Expr::Call(call) = expr {
                if let Some(mut old_arg) = get_old_data(call) {
                    // if it's a call to old() then add to list of
                    // old expressions and continue to check the
                    // argument.

                    self.visit_expr_mut(&mut old_arg);

                    let id = self.last_id;
                    self.last_id += 1;

                    let old_var_name = format!("__contract_old_{}", id);

                    let old_expr = OldExpr { name: old_var_name.clone(), expr: old_arg };

                    self.olds.push(old_expr);

                    // override the original expression with the new variable
                    // identifier

                    *expr = {
                        let span = expr.span();

                        let ident = syn::Ident::new(&old_var_name, span);

                        let toks = quote::quote! {#ident };

                        syn::parse(toks.into()).unwrap()
                    };
                } else {
                    // otherwise continue visiting the expression call
                    visitor::visit_expr_call_mut(self, call);
                }
            } else {
                visitor::visit_expr_mut(self, expr);
            }
        }
    }

    let mut extractor = OldExtractor { last_id: 0, olds: vec![] };

    use visitor::VisitMut;
    for a in item.attrs.iter_mut() {
        let name = a.path.segments.last().unwrap().ident.to_string();
        match name.as_str() {
            "ensures" => {
                let mut arg =
                    a.parse_args::<Expr>().expect("Ensures clause must have an argument.");
                extractor.visit_expr_mut(&mut arg);
                let toks: TokenStream2 = quote::quote! { (#arg) };
                let attr_new = syn::Attribute {
                    pound_token: a.pound_token.clone(),
                    style: a.style.clone(),
                    bracket_token: a.bracket_token.clone(),
                    path: a.path.clone(),
                    tokens: toks,
                };
                *a = attr_new;
            }
            _ => {}
        }
    }
    extractor.olds
}

// Converts all "[#kani::ensures(...)]" attributes to "#kani::postcondition(...)" statement tokens.
pub fn extract_ensures_as_postconditions(attributes: &Vec<Attribute>) -> TokenStream2 {
    attributes
        .iter()
        .filter_map(|a| {
            let name = a.path.segments.last().unwrap().ident.to_string();
            match name.as_str() {
                "ensures" => {
                    let arg =
                        a.parse_args::<Expr>().expect("Ensures clause must have an argument.");
                    Some(quote! {kani::postcondition(#arg);})
                }
                _ => None,
            }
        })
        .collect()
}

// Converts all "[#kani::requires(...)]" attributes to "#kani::precondition(...)" statement tokens.
pub fn extract_requires_as_preconditions(attributes: &Vec<Attribute>) -> TokenStream2 {
    attributes
        .iter()
        .filter_map(|a| {
            let name = a.path.segments.last().unwrap().ident.to_string();
            match name.as_str() {
                "requires" => {
                    let arg =
                        a.parse_args::<Expr>().expect("Requires clause must have an argument.");
                    Some(quote!(kani::precondition(#arg);))
                }
                _ => None,
            }
        })
        .collect()
}

// Return all attributes that are not "[#kani::requires(...)]" or "[#kani::ensures(...)]".
pub fn extract_non_contract_attributes(attributes: &Vec<Attribute>) -> TokenStream2 {
    attributes
        .iter()
        .filter_map(|a| {
            let name = a.path.segments.last().unwrap().ident.to_string();
            match name.as_str() {
                "ensures" | "requires" => None,
                _ => Some(quote! {#a}),
            }
        })
        .collect()
}

fn positional_arg(i: usize) -> Ident {
    format_ident!("__arg{}", i)
}

// Returns the list of function arguments from the function signature.
pub fn extract_function_args(sig: &Signature) -> TokenStream2 {
    sig.inputs
        .iter()
        .enumerate()
        .map(|(i, arg)| match arg {
            FnArg::Typed(arg) => {
                if let syn::Pat::Ident(syn::PatIdent { ident, .. }) = &*arg.pat {
                    quote!(#ident)
                } else {
                    positional_arg(i).into_token_stream()
                }
            }
            FnArg::Receiver(syn::Receiver { self_token, .. }) => quote!(#self_token), // Ignore arguments like "self", etc.
        })
        .collect()
}

struct SelfReplacer<'a> {
    replace_with: &'a syn::Ident,
}

impl syn::visit_mut::VisitMut for SelfReplacer<'_> {
    fn visit_ident_mut(&mut self, i: &mut Ident) {
        if i == "self" {
            *i = self.replace_with.clone();
        }
    }
}

fn ty_contains_impl_trait(ty: &syn::Type) -> bool {
    use syn::visit::Visit;

    struct TyContainsImplTrait {
        seen_impl_trait: bool,
    }

    impl syn::visit::Visit<'_> for TyContainsImplTrait {
        fn visit_type_impl_trait(&mut self, _: &syn::TypeImplTrait) {
            self.seen_impl_trait = true;
        }
    }

    let mut vis = TyContainsImplTrait { seen_impl_trait: false };
    vis.visit_type(ty);
    vis.seen_impl_trait
}

pub fn create_body_closure(func: &syn::ItemFn) -> TokenStream2 {
    let is_method = func.sig.receiver().is_some();

    // If the function has a receiver (e.g. `self`, `&mut self`, or `self: Box<Self>`) rename it
    // to `this` within the closure

    let mut block = func.block.clone();
    let mut closure_args = vec![];
    let mut arg_names = vec![];

    if is_method {
        // `mixed_site` makes the identifier hygienic so it won't collide with a local variable
        // named `this`.
        let this_ident = syn::Ident::new("this", Span::mixed_site());

        let mut receiver = func.sig.inputs[0].clone();
        match receiver {
            // self, &self, &mut self
            syn::FnArg::Receiver(rcv) => {
                // The `Self` type.
                let self_ty = Box::new(syn::Type::Path(syn::TypePath {
                    qself: None,
                    path: syn::Path::from(syn::Ident::new("Self", rcv.span())),
                }));

                let ty = if let Some((and_token, ref lifetime)) = rcv.reference {
                    Box::new(syn::Type::Reference(syn::TypeReference {
                        and_token,
                        lifetime: lifetime.clone(),
                        mutability: rcv.mutability,
                        elem: self_ty,
                    }))
                } else {
                    self_ty
                };

                let pat_mut = if rcv.reference.is_none() { rcv.mutability } else { None };

                // this: [& [mut]] Self
                let new_rcv = syn::PatType {
                    attrs: rcv.attrs.clone(),
                    pat: Box::new(syn::Pat::Ident(syn::PatIdent {
                        attrs: vec![],
                        by_ref: None,
                        mutability: pat_mut,
                        ident: this_ident.clone(),
                        subpat: None,
                    })),
                    colon_token: syn::Token![:](rcv.span()),
                    ty,
                };

                receiver = syn::FnArg::Typed(new_rcv);
            }

            // self: Box<Self>
            syn::FnArg::Typed(ref mut pat) => {
                if let syn::Pat::Ident(ref mut ident) = *pat.pat {
                    if ident.ident == "self" {
                        ident.ident = this_ident.clone();
                    }
                }
            }
        }

        closure_args.push(receiver);

        match &func.sig.inputs[0] {
            syn::FnArg::Receiver(receiver) => {
                arg_names.push(syn::Ident::new("self", receiver.self_token.span()));
            }
            syn::FnArg::Typed(pat) => {
                if let syn::Pat::Ident(ident) = &*pat.pat {
                    arg_names.push(ident.ident.clone());
                } else {
                    // Non-trivial receiver pattern => do not capture
                    closure_args.pop();
                }
            }
        };

        // Replace any references to `self` in the function body with references to `this`.
        syn::visit_mut::visit_block_mut(
            &mut SelfReplacer { replace_with: &this_ident },
            &mut block,
        );
    }
    // Any function arguments of the form `ident: ty` become closure arguments and get passed
    // explicitly. More complex ones, e.g. pattern matching like `(a, b): (u32, u32)`, are
    // captured instead.
    let args = func.sig.inputs.iter().skip(if is_method { 1 } else { 0 });
    for arg in args {
        match arg {
            syn::FnArg::Receiver(_) => unreachable!("Multiple receivers?"),

            syn::FnArg::Typed(syn::PatType { pat, ty, .. }) => {
                if !ty_contains_impl_trait(ty) {
                    if let syn::Pat::Ident(ident) = &**pat {
                        let ident_str = ident.ident.to_string();

                        // Any function argument identifier starting with '_' signals
                        // that the binding will not be used.
                        if !ident_str.starts_with('_') || ident_str.starts_with("__") {
                            arg_names.push(ident.ident.clone());
                            closure_args.push(arg.clone());
                        }
                    }
                }
            }
        }
    }

    let ret_ty = match &func.sig.output {
        ReturnType::Type(_, ty) => {
            let span = ty.span();
            match ty.as_ref() {
                syn::Type::ImplTrait(_) => quote::quote! {},
                ty => quote::quote_spanned! { span=>
                    -> #ty
                },
            }
        }
        ReturnType::Default => quote::quote! {},
    };

    let closure_args = closure_args.iter();
    let arg_names = arg_names.iter();

    quote::quote! {
        #[allow(unused_mut)]
        let mut run = |#(#closure_args),*| #ret_ty #block;

        let ret = run(#(#arg_names),*);
    }
}

/// Given a function `foo`, this function creates a new function with name
/// `foo_<uuid>`, where <uuid> is a unique identifier.
/// The new function has the same function arguments and the same function body
/// as the original function `foo`.
pub fn convert_to_inner_function(item: &ItemFn) -> (Ident, TokenStream2) {
    let fn_sig = &item.sig;
    let stmts = &item.block.stmts;
    let mut sig = fn_sig.clone();
    let name = format!("{}_{}", fn_sig.ident.clone().to_string(), Uuid::new_v4()).replace("-", "_");
    let ident = Ident::new(name.as_str(), Span::call_site());
    sig.ident = ident.clone();
    let inner_fn = quote! {
        #sig {
            #(#stmts)*
        }
    };
    (ident, inner_fn)
}
