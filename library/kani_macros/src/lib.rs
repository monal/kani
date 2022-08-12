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
mod contract;
use syn::spanned::Spanned;

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
pub fn ensures(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // When the config is not Kani, we should leave the function alone
    item
}

#[cfg(kani)]
#[proc_macro_attribute]
/// If config is Kani, `#[kani::ensures(arg)]` specifies a postcondition on the function.
/// The postcondition is treated as part of the function's "contract" specification.
/// arg - Takes in a boolean expression that represents the precondition.
/// The following transformations take place during macro expansion:
/// 1) All `#[kani::requires(arg)]` attributes gets translated to `kani::precondition(arg)` and
///     gets injected to the body of the function right before the actual body begins.
/// 2) All `#[kani::ensures(arg)]` attributes gets translated to `kani::postcondition(arg)` and
///     gets injected to the body of the function, after the actual body begins.
/// 3) The body of the original function (say function `foo`) gets wrapped into a new function
///     with name `foo_<uuid>(...)` and the new function is subsequently called.
///     This is done to handle the return value of the original function
///     as `kani:postcondition(..)` gets injected after the body of the function.
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    let parsed_attr = syn::parse_macro_input!(attr as syn::Expr);

    // Extract other contract clauses from "item"
    let mut parsed_item = syn::parse_macro_input!(item as syn::ItemFn);
    let other_attributes = parsed_item.attrs.clone();
    let pre = contract::extract_requires_as_preconditions(&other_attributes);

    // Extract components of the function from "item"
    let fn_vis = parsed_item.vis.clone();
    let fn_sig = parsed_item.sig.clone();
    // let args = contract::extract_function_args(fn_sig);
    let olds_expr: Vec<contract::OldExpr> = contract::extract_old_calls(&mut parsed_item);
    let olds = {
        let mut toks = proc_macro2::TokenStream::new();

        for old in olds_expr {
            let span = old.expr.span();

            let name = syn::Ident::new(&old.name, span);

            let expr = old.expr;

            let binding = quote::quote_spanned! { span=>
                let #name = #expr;
            };

            toks.extend(Some(binding));
        }

        toks
    };
    let post_attributes = parsed_item.attrs.clone();
    let post = contract::extract_ensures_as_postconditions(&post_attributes);
    // Create inner function
    // let (inner_ident, inner_fn) = contract::convert_to_inner_function(&parsed_item);
    let body = if post.is_empty() {
        let block = parsed_item.block;
        quote::quote! { let ret = #block; }
    } else {
        contract::create_body_closure(&parsed_item)
    };
    quote::quote! {
        // #other
        #fn_vis #fn_sig {
            #pre
            #olds
            #body
            kani::postcondition(#parsed_attr);
            #post
            ret
        }
    }
    .into()
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
/// The following transformations take place during macro expansion:
/// 1) All `#[kani::requires(arg)]` attributes gets translated to `kani::precondition(arg)` and
///     gets injected to the body of the function right before the actual body begins.
/// 2) All `#[kani::ensures(arg)]` attributes gets translated to `kani::postcondition(arg)` and
///     gets injected to the body of the function, after the actual body begins.
/// 3) The body of the original function (say function `foo`) gets wrapped into a new function
///     with name `foo_<uuid>(...)` and the new function is subsequently called.
///     This is done to handle the return value of the original function
///     as `kani:postcondition(..)` gets injected after the body of the function.
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    let parsed_attr = syn::parse_macro_input!(attr as syn::Expr);

    // Extract other contract clauses from "item"
    let mut parsed_item = syn::parse_macro_input!(item as syn::ItemFn);
    let other_attributes = parsed_item.attrs.clone();
    let pre = contract::extract_requires_as_preconditions(&other_attributes);
    let non_contract = contract::extract_non_contract_attributes(&other_attributes);
    // Extract components of the function from "item"
    let fn_vis = parsed_item.vis.clone();
    let fn_sig = parsed_item.sig.clone();
    // let args = contract::extract_function_args(fn_sig);
    let olds_expr: Vec<contract::OldExpr> = contract::extract_old_calls(&mut parsed_item);
    let olds = {
        let mut toks = proc_macro2::TokenStream::new();

        for old in olds_expr {
            let span = old.expr.span();
            let name = syn::Ident::new(&old.name, span);
            let expr = old.expr;
            let binding = quote::quote! {
                let #name = #expr;
            };
            toks.extend(binding);
        }
        toks
    };
    let post_attributes = parsed_item.attrs.clone();
    let post = contract::extract_ensures_as_postconditions(&post_attributes);
    // Create inner function
    // let (inner_ident, inner_fn) = contract::convert_to_inner_function(&parsed_item);
    let body = if post.is_empty() {
        let block = parsed_item.block;
        quote::quote! { let ret = #block; }
    } else {
        contract::create_body_closure(&parsed_item)
    };

    quote::quote! {
        #non_contract
        #fn_vis #fn_sig {
            kani::precondition(#parsed_attr);
            #pre
            #olds
            if kani::replace_function_body() {
                let ret = kani::any();
                #post
                ret
            } else {
                #body
                #post
                ret
            }
        }
    }
    .into()
}

/// The attribute '#[kani::assigns(arg1, arg2, ...)]' defines the write set of the function.
/// arg - Zero or more comma-separated “targets” which can be variables or references.
#[cfg(kani)]
#[proc_macro_attribute]
pub fn assigns(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse comma-separated argument 'arg'
    let parsed_attr: Vec<syn::Ident> =
        syn::parse_macro_input!(attr with syn::punctuated::Punctuated::<syn::Ident, syn::Token![,]>::parse_terminated)
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
