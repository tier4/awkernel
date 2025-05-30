//! The futures-rs procedural macro implementations.

#![doc(test(
    no_crate_inject,
    attr(
        deny(warnings, rust_2018_idioms, single_use_lifetimes),
        allow(dead_code, unused_assignments, unused_variables)
    )
))]

use proc_macro::TokenStream;

mod select;

/// The `select!` macro.
#[proc_macro]
pub fn select_internal(input: TokenStream) -> TokenStream {
    crate::select::select(input)
}
