// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// #![feature(register_tool)]
// #![register_tool(kanitool)]
// Frustratingly, it's not enough for our crate to enable these features, because we need all
// downstream crates to enable these features as well.
// So we have to enable this on the commandline (see kani-rustc) with:
//   RUSTFLAGS="-Zcrate-attr=feature(register_tool) -Zcrate-attr=register_tool(kanitool)"

// proc_macro::quote is nightly-only, so we'll cobble things together instead
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use proc_macro2::{Ident, Span};
use quote::quote;
use syn::{
    parse_macro_input, parse_quote, punctuated, Attribute, Expr, FnArg, ItemFn, Signature, Token,
};
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

fn extract_requires_as_preconditions(attributes: &Vec<Attribute>) -> TokenStream2 {
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

fn extract_ensures_as_postconditions(attributes: &Vec<Attribute>) -> TokenStream2 {
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

fn extract_non_contract_attributes(attributes: &Vec<Attribute>) -> TokenStream2 {
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
fn extract_function_args(sig: &Signature) -> Vec<syn::Pat> {
    sig.inputs
        .iter()
        .filter_map(|x| match x {
            FnArg::Typed(syn::PatType { pat, .. }) => Some(*pat.clone()),
            _ => None,
        })
        .collect()
}

fn convert_to_inner_function(item: &ItemFn) -> (Ident, TokenStream2) {
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

#[cfg(not(kani))]
#[proc_macro_attribute]
pub fn requires(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // When the config is not Kani, we should leave the function alone
    item
}

#[cfg(kani)]
#[proc_macro_attribute]
/// If config is Kani, `#[kani::requires(arg)]` adds a precondition on the function.
/// The precondition is treated as part of the function's "contract" specification.
/// It is later "assumed" or "asserted" depending on whether Kani is checking
///   1) if a function satisfies it contract (contract enforcement), or
///   2) if Kani is replacing a function with its contract (contract replacement).
/// arg - Takes in a boolean expression that represents the precondition.
/// The following transformations take place during macro expansion:
/// 1) All `#[kani::requires(arg)]` attributes gets translated to `kani::precondition(arg)` and
///     gets injected to the body of the function right before the actual body begins.
/// 2) All `#[kani::ensures(arg)]` attributes gets translated to `kani::postcondition(arg)` and
///     gets injected to the body of the function, after the actual body begins.
/// 3) The body of the original function (say function `foo`) gets wrapped into a new function
///     with name `foo_<uuid>(...)` to handle return values once the calls to `kani:postcondition(..)`
///     gets injected.
/// 4) The inner function is `foo_<uuid>(...)` is stored into a local variable and returned.
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    let parsed_attr = parse_macro_input!(attr as Expr);

    // Extract other contract clauses from "item"
    let parsed_item = parse_macro_input!(item as ItemFn);
    let other_attributes = &parsed_item.attrs;
    let pre = extract_requires_as_preconditions(&other_attributes);
    let post = extract_ensures_as_postconditions(&other_attributes);
    let non_contract = extract_non_contract_attributes(&other_attributes);

    // Create inner function
    let (inner_ident, inner_fn) = convert_to_inner_function(&parsed_item);

    // Extract components of the function from "item"
    let fn_vis = &parsed_item.vis;
    let fn_sig = &parsed_item.sig;
    let args = extract_function_args(fn_sig);
    let rt = match &parsed_item.sig.output {
        syn::ReturnType::Type(_, ty) => *ty.clone(),
        syn::ReturnType::Default => parse_quote! { () },
    };

    quote::quote! {
        #non_contract
        #fn_vis #fn_sig {
            kani::precondition(#parsed_attr);
            #pre
            #inner_fn
            let ret = if kani::replace_function_body() {
                kani::any()
            } else {
                #inner_ident(#(#args,)*)
            };
            #post
            ret
        }
    }
    .into()
}

#[cfg(not(kani))]
#[proc_macro_attribute]
pub fn ensures(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // When the config is not Kani, we should leave the function alone
    item
}

#[cfg(kani)]
#[proc_macro_attribute]
/// If config is Kani, `#[kani::ensures(arg)]` adds a postcondition on the function.
/// The postcondition is treated as part of the function's "contract" specification.
/// It is later "asserted" or "assumed" depending on whether Kani is checking
///   1) if a function satisfies it contract (contract enforcement), or
///   2) if Kani is replacing a function with its contract (contract replacement).
/// arg - Takes in a boolean expression that represents the precondition.
/// The following transformations take place during macro expansion:
/// 1) All `#[kani::requires(arg)]` attributes gets translated to `kani::precondition(arg)` and
///     gets injected to the body of the function right before the actual body begins.
/// 2) All `#[kani::ensures(arg)]` attributes gets translated to `kani::postcondition(arg)` and
///     gets injected to the body of the function, after the actual body begins.
/// 3) The body of the original function (say function `foo`) gets wrapped into a new function
///     with name `foo_<uuid>(...)` to handle return values once the calls to `kani:postcondition(..)`
///     gets injected.
/// 4) The inner function is `foo_<uuid>(...)` is stored into a local variable and returned.
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    let parsed_attr = parse_macro_input!(attr as Expr);

    // Extract other contract clauses from "item"
    let parsed_item = parse_macro_input!(item as ItemFn);
    let other_attributes = &parsed_item.attrs;
    let pre = extract_requires_as_preconditions(&other_attributes);
    let post = extract_ensures_as_postconditions(&other_attributes);

    // Create inner function
    let (inner_ident, inner_fn) = convert_to_inner_function(&parsed_item);

    // Extract components of the function from "item"
    let fn_vis = &parsed_item.vis;
    let fn_sig = &parsed_item.sig;
    let args = extract_function_args(fn_sig);
    let rt = &parsed_item.sig.output;

    quote::quote! {
        // #other
        #fn_vis #fn_sig {
            #pre
            #inner_fn
            let ret = if kani::replace_function_body() {
                kani::any()
            } else {
                #inner_ident(#(#args,)*)
            };
            kani::postcondition(#parsed_attr);
            #post
            ret
        }
    }
    .into()
}

#[cfg(not(kani))]
#[proc_macro_attribute]
pub fn assigns(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // When the config is not Kani, we should leave the function alone
    item
}

/// The attribute '#[kani::assigns(arg1, arg2, ...)]' defines the write set of the function.
/// arg - Zero or more comcma-separated “targets” is either a variable, a dereference expression,
///     a member expression, an "object", a slice expression.
#[cfg(kani)]
#[proc_macro_attribute]
pub fn assigns(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse 'arg'
    let parsed_attr: Vec<syn::Expr> =
        parse_macro_input!(attr with punctuated::Punctuated::<syn::Expr, Token![,]>::parse_terminated)
            .into_iter()
            .collect();

    // Parse 'item' and extract out the function and the remaining attributes.
    let parsed_item = syn::parse_macro_input!(item as syn::ItemFn);

    quote::quote! {
        #[kanitool::assigns(#(#parsed_attr,)*)]
        #parsed_item
    }
    .into()
}
