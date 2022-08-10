// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// Utility functions for macro expansion of function contract clauses.
use proc_macro2::TokenStream as TokenStream2;
use proc_macro2::{Ident, Span};
use quote::quote;
use syn::{Attribute, Expr, FnArg, ItemFn, Signature};
use uuid::Uuid;

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

// Returns the list of function arguments from the function signature.
pub fn extract_function_args(sig: &Signature) -> Vec<syn::Pat> {
    sig.inputs
        .iter()
        .filter_map(|x| match x {
            FnArg::Typed(syn::PatType { pat, .. }) => Some(*pat.clone()),
            _ => None, // Ignore arguments like "self", etc.
        })
        .collect()
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
