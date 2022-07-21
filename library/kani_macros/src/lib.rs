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
use syn::parse_quote_spanned;
use syn::spanned::Spanned;
use uuid::Uuid;
use quote::quote;

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
    // When the config is not kani, we should leave the function alone
    item
}

/// Set postcondition of a function using a function contract
/// The attribute '#[kani::ensures(arg)]' can only be called alongside '#[kani::proof]'.
/// arg - Takes in a boolean expression that represents the postcondition.
#[cfg(kani)]
#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut result = TokenStream::new();

    // Convert item token stream to AST
    let item_ast = syn::parse::<syn::ItemFn>(item.clone()).unwrap();
    let item_span = item_ast.span();
    let item_name = item_ast.sig.ident;
    let attr_ast = syn::parse::<syn::Expr>(attr.clone()).unwrap();
    let spec_span = attr_ast.span();
    let spec_id = Uuid::new_v4();
    let spec_fn_name =
        syn::Ident::new(&format!("contract_{}_ensures_{}", item_name, spec_id), spec_span);

    let mut spec_item: syn::ItemFn = parse_quote_spanned! {item_span =>
        fn #item_name() -> bool {
            !!((#attr_ast): bool)
        }
    };
    spec_item.sig.generics = item_ast.sig.generics.clone();
    spec_item.sig.inputs = item_ast.sig.inputs.clone();
    let output_ty = match &item_ast.sig.output {
        syn::ReturnType::Default => parse_quote_spanned!(item_span=> ()),
        syn::ReturnType::Type(_, ty) => ty.clone(),
    };
    let fn_arg = syn::FnArg::Typed(syn::PatType {
        attrs: Vec::new(),
        pat: Box::new(parse_quote_spanned!(item_span => result)),
        colon_token: syn::Token![:](item_ast.sig.output.span()),
        ty: output_ty,
    });
    spec_item.sig.inputs.push(fn_arg);
    let spec_item_tokens = TokenStream::from(quote!(#spec_item));
    result.extend(spec_item_tokens);
    
    // Translate #[kani::ensures(arg)] to #[kanitool::ensures(arg)]
    let insert_string = "#[kanitool::ensures(".to_owned() + &spec_fn_name.to_string() + ")]";
    result.extend(insert_string.parse::<TokenStream>().unwrap());

    result.extend(item);
    result
}
