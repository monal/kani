// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// #![feature(register_tool)]
// #![register_tool(kanitool)]
// Frustratingly, it's not enough for our crate to enable these features, because we need all
// downstream crates to enable these features as well.
// So we have to enable this on the commandline (see kani-rustc) with:
//   RUSTFLAGS="-Zcrate-attr=feature(register_tool) -Zcrate-attr=register_tool(kanitool)"

// proc_macro::quote is nightly-only, so we'll cobble things together instead
#![feature(proc_macro)]
use proc_macro::TokenStream;
pub mod contract;
use contract::ContractAttributes;
use proc_macro2::{Ident, Span};
use uuid::Uuid;

#[cfg(all(not(kani), not(test)))]
#[proc_macro_attribute]
pub fn proof(_attr: TokenStream, _item: TokenStream) -> TokenStream {
    // Not-Kani, Not-Test means this code shouldn't exist, return nothing.
    TokenStream::new()
}

#[cfg(all(not(kani), test))]
#[proc_macro_attribute]
pub fn proof(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // Leave the code intact, so it can be easily be edited in an IDE,
    // but outside Kani, this code is likely never called.
    let mut result = TokenStream::new();

    result.extend("#[allow(dead_code)]".parse::<TokenStream>().unwrap());
    result.extend(item);
    result
    // quote!(
    //     #[allow(dead_code)]
    //     $item
    // )
}

#[cfg(kani)]
#[proc_macro_attribute]
pub fn proof(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut result = TokenStream::new();

    assert!(attr.to_string().len() == 0, "#[kani::proof] does not take any arguments");
    result.extend("#[kanitool::proof]".parse::<TokenStream>().unwrap());
    // no_mangle is a temporary hack to make the function "public" so it gets codegen'd
    result.extend("#[no_mangle]".parse::<TokenStream>().unwrap());
    result.extend(item);
    result
    // quote!(
    //     #[kanitool::proof]
    //     $item
    // )
}

#[cfg(not(kani))]
#[proc_macro_attribute]
pub fn unwind(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // When the config is not kani, we should leave the function alone
    item
}

/// Set Loop unwind limit for proof harnesses
/// The attribute '#[kani::unwind(arg)]' can only be called alongside '#[kani::proof]'.
/// arg - Takes in a integer value (u32) that represents the unwind value for the harness.
#[cfg(kani)]
#[proc_macro_attribute]
pub fn unwind(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut result = TokenStream::new();

    // Translate #[kani::unwind(arg)] to #[kanitool::unwind(arg)]
    let insert_string = "#[kanitool::unwind(".to_owned() + &attr.clone().to_string() + ")]";
    result.extend(insert_string.parse::<TokenStream>().unwrap());

    result.extend(item);
    result
}

#[cfg(not(kani))]
#[proc_macro_attribute]
/// Ignores #[kani::requires(arg)] when config is not Kani
pub fn requires(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // When the config is not kani, we should leave the function alone
    item
}

#[cfg(kani)]
#[proc_macro_attribute]
/// If config is Kani, `#[kani::requires(arg)]` attaches a precondition to the function.
/// arg - Takes in a boolean expression that represents the precondition.
/// Preconditions are treated as part of the "contract" of a function.
/// Depending on the context, it is either asserted (or checked) by Kani to ensure that the function respects its contract, 
///     or assumed when a function is replaced by its contract.
/// #[kani::requires(arg)]
/// ...
/// fn foo {...} ...
///     gets translated to 
/// fn foo {
///     kani::precondition(arg);
///     fn foo_<uuid> { //...body of the function... }
///     let ret = foo(...// function args);
///     ret
/// }
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse 'arg'
    let parsed_attr = syn::parse_macro_input!(attr as syn::Expr);

    // Parse 'item' and extract out the function and the remaining attributes.
    let parsed_item = syn::parse_macro_input!(item as syn::ItemFn);
    let other_attributes = parsed_item.attrs;
    let contract_attributes = ContractAttributes::new(other_attributes);
    let pre = contract_attributes.extract_preconditions();
    let post = contract_attributes.extract_postconditions();
    let other = contract_attributes.extract_other_attributes();
    let fn_vis = parsed_item.vis;
    let fn_sig = parsed_item.sig;
    let body_stmts = parsed_item.block.stmts;
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

    quote::quote! {
        #other
        #fn_vis #fn_sig {
            kani::precondition(#parsed_attr, "pre");
            #pre
            #inner_sig {
                #(#body_stmts)*
            }
            let ret = #inner_sig_ident(#(#fn_args)*);
            #post
            ret
        }
    }
    .into()
}

#[cfg(not(kani))]
#[proc_macro_attribute]
pub fn ensures(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // When the config is not kani, we should leave the function alone
    item
}


/// The attribute '#[kani::requires(arg)]' defines a function contract clause for
/// setting the postcondition of a function.
/// arg - Takes in a boolean expression that represents the postcondition.
#[cfg(kani)]
#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse 'arg'
    let parsed_attr = syn::parse_macro_input!(attr as syn::Expr);

    // Parse 'item' and extract out the function and the remaining attributes.
    let parsed_item = syn::parse_macro_input!(item as syn::ItemFn);
    let other_attributes = parsed_item.attrs;
    let contract_attributes = ContractAttributes::new(other_attributes);
    let pre = contract_attributes.extract_preconditions();
    let post = contract_attributes.extract_postconditions();
    let other = contract_attributes.extract_other_attributes();
    let fn_vis = parsed_item.vis;
    let fn_sig = parsed_item.sig;
    let body_stmts = parsed_item.block.stmts;
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

    quote::quote! {
        #other
        #fn_vis #fn_sig {
            #pre
            #inner_sig {
                #(#body_stmts)*
            }
            let ret = #inner_sig_ident(#(#fn_args)*);
            kani::postcondition(#parsed_attr, "post");
            #post
            ret
        }
    }
    .into()
}

#[cfg(not(kani))]
#[proc_macro_attribute]
pub fn assigns(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // When the config is not kani, we should leave the function alone
    item
}


/// The attribute '#[kani::requires(arg)]' defines a function contract clause for
/// setting the postcondition of a function.
/// arg - Takes in a boolean expression that represents the postcondition.
#[cfg(kani)]
#[proc_macro_attribute]
pub fn assigns(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse 'arg'
    let parsed_attr = syn::parse_macro_input!(attr as syn::Expr);

    // Parse 'item' and extract out the function and the remaining attributes.
    let parsed_item = syn::parse_macro_input!(item as syn::ItemFn);

    quote::quote! {
        #[kanitool::assigns(#parsed_attr)]
        #parsed_item
    }
    .into()
}
