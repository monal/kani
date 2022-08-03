// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
use proc_macro::TokenStream;
use syn::{Attribute, Signature};
use proc_macro2::{Ident, Span};
use uuid::Uuid;

pub struct ContractAttributes {
    attributes: Vec<Attribute>,
}

impl ContractAttributes {
    pub fn new(attributes: Vec<Attribute>) -> Self {
        Self { attributes }
    }

    pub fn extract_preconditions(&self) -> proc_macro2::TokenStream {
        self.attributes
            .iter()
            .filter_map(|a| {
                let name = a.path.segments.last().unwrap().ident.to_string();
                match name.as_str() {
                    "requires" => {
                        let arg = a
                            .parse_args::<syn::Expr>()
                            .expect("requires clause must have an argument.");
                        Some(quote::quote! { kani::precondition(#arg, "pre");})
                    }
                    _ => None,
                }
            })
            .collect()
    }

    pub fn extract_postconditions(&self) -> proc_macro2::TokenStream {
        self.attributes
            .iter()
            .filter_map(|a| {
                let name = a.path.segments.last().unwrap().ident.to_string();

                match name.as_str() {
                    "ensures" => {
                        let arg = a
                            .parse_args::<syn::Expr>()
                            .expect("ensures clause must have an argument.");
                        Some(quote::quote! { kani::postcondition(#arg, "post");})
                    }
                    _ => None,
                }
            })
            .collect()
    }

    pub fn extract_other_attributes(&self) -> proc_macro2::TokenStream {
        self.attributes
            .iter()
            .filter_map(|a| {
                let name = a.path.segments.last().expect("Should have something").ident.to_string();
                match name.as_str() {
                    "ensures" => None,
                    "requires" => None,
                    _ => Some(quote::quote! {#a}),
                }
            })
            .collect()
    }
}

pub fn convert_fn_to_inner_fn(fn_sig: Signature ) {
    let mut inner_sig = fn_sig.clone();
    let new_fn_name =
        format!("{}_{}", fn_sig.ident.clone().to_string(), Uuid::new_v4()).replace("-", "_");
    let inner_sig_ident = Ident::new(new_fn_name.as_str(), Span::call_site());
    inner_sig.ident = inner_sig_ident.clone();
    let fn_args: Vec<syn::Pat> = fn_sig
        .clone()
        .inputs
        .iter()
        .filter_map(|x| match x {
            syn::FnArg::Typed(syn::PatType { pat, ty, .. }) => Some(*pat.clone()),
            _ => None,
        })
        .collect();
    
}