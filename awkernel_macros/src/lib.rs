//! Procedural macros for Awkernel.

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, spanned::Spanned, ItemFn};

/// Marks an `async fn` as the entry point of the userland.
///
/// The kernel spawns it as the first task once it has booted.
/// The function must be `async`, take no arguments, and return
/// `Result<(), Cow<'static, str>>`.
///
/// ```ignore
/// #[awkernel::main]
/// async fn main() -> Result<(), alloc::borrow::Cow<'static, str>> {
///     Ok(())
/// }
/// ```
#[proc_macro_attribute]
pub fn main(args: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);

    if !args.is_empty() {
        return syn::Error::new(
            proc_macro2::TokenStream::from(args).span(),
            "`#[awkernel::main]` takes no arguments",
        )
        .to_compile_error()
        .into();
    }
    if func.sig.asyncness.is_none() {
        return syn::Error::new(func.sig.span(), "the entry point must be an `async fn`")
            .to_compile_error()
            .into();
    }
    if !func.sig.inputs.is_empty() {
        return syn::Error::new(
            func.sig.inputs.span(),
            "the entry point must not take arguments",
        )
        .to_compile_error()
        .into();
    }
    if !func.sig.generics.params.is_empty() {
        return syn::Error::new(
            func.sig.generics.span(),
            "the entry point must not be generic",
        )
        .to_compile_error()
        .into();
    }

    let name = &func.sig.ident;

    // The symbol is resolved at link time by the kernel (`awkernel::UserMain`).
    quote! {
        #func

        #[no_mangle]
        pub fn __awkernel_user_main() -> ::core::pin::Pin<
            ::alloc::boxed::Box<
                dyn ::core::future::Future<
                        Output = ::core::result::Result<
                            (),
                            ::alloc::borrow::Cow<'static, str>,
                        >,
                    > + ::core::marker::Send,
            >,
        > {
            ::alloc::boxed::Box::pin(#name())
        }
    }
    .into()
}
