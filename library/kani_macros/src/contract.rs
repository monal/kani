// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
use proc_macro::TokenStream;
use syn::{Attribute, ItemFn};

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
                let arg = a.parse_args::<syn::Expr>().unwrap();
                match name.as_str() {
                    "requires" => Some(quote::quote! { kani::precondition(#arg);}),
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
                let arg = a.parse_args::<syn::Expr>().unwrap();
                match name.as_str() {
                    "ensures" => Some(quote::quote! { kani::postcondition(#arg);}),
                    _ => None,
                }
            })
            .collect()
    }

    pub fn extract_write_set(&self) -> proc_macro2::TokenStream {
        self.attributes
            .iter()
            .filter_map(|a| {
                let name = a.path.segments.last().unwrap().ident.to_string();
                let arg = a.parse_args::<syn::Expr>().unwrap();
                match name.as_str() {
                    "assigns" => Some(quote::quote! { kani::write_set(#arg);}),
                    _ => None,
                }
            })
            .collect()
    }

    pub fn extract_other_attributes(&self) -> proc_macro2::TokenStream {
        self.attributes
            .iter()
            .filter_map(|a| {
                let name = a.path.segments.last().unwrap().ident.to_string();
                match name.as_str() {
                    "ensures" => None,
                    "requires" => None,
                    "assigns" => None,
                    _ => Some(quote::quote! {#a}),
                }
            })
            .collect()
    }
}
