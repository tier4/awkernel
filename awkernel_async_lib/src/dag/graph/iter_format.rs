//! Formatting utils
//!
//! This file includes portions of code from petgraph under Apache License 2.0 OR the MIT License.
//!
//! Modifications include:
//! - Adapted for no-std
//!
//! This file is dual-licensed under the Apache License 2.0 OR the MIT License,
//! at your option. This means you can use, modify, and distribute this file under
//! either of these licenses.
//!
//! # LICENSE (Apache-2.0 OR MIT)
//!
//! ```text
//! Licensed under either of
//!
//! - Apache License, Version 2.0 (LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0)
//! - MIT License (LICENSE-MIT or https://opensource.org/licenses/MIT)
//!
//! at your option. This file may not be copied, modified, or distributed except
//! according to those terms.
//! ```
//!
//! # LICENSE (Apache-2.0)
//!
//! ```text
//! Apache License
//! Copyright 2015 bluss, github:petgraph:release-team, ABorgna
//!
//! Licensed under the Apache License, Version 2.0 (the "License");
//! you may not use this file except in compliance with the License.
//! You may obtain a copy of the License at
//!
//! http://www.apache.org/licenses/LICENSE-2.0
//!
//! Unless required by applicable law or agreed to in writing, software
//! distributed under the License is distributed on an "AS IS" BASIS,
//! WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//! See the License for the specific language governing permissions and
//! limitations under the License.
//!
//! # LICENSE (MIT)
//!
//! ```text
//! The MIT License (MIT)
//!
//! Copyright (c) 2015 bluss, github:petgraph:release-team, ABorgna
//!
//! Permission is hereby granted, free of charge, to any person obtaining a copy
//! of this software and associated documentation files (the "Software"), to deal
//! in the Software without restriction, including without limitation the rights
//! to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//! copies of the Software, and to permit persons to whom the Software is
//! furnished to do so, subject to the following conditions:
//!
//! The above copyright notice and this permission notice shall be included in all
//! copies or substantial portions of the Software.
//!
//! THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//! IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//! FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//! AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//! LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//! OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
//! SOFTWARE.
//! ```

use core::cell::RefCell;
use core::fmt::{self};

/// Format the iterator like a map
pub struct DebugMap<F>(pub F);

impl<F, I, K, V> fmt::Debug for DebugMap<F>
where
    F: Fn() -> I,
    I: IntoIterator<Item = (K, V)>,
    K: fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries((self.0)()).finish()
    }
}

/// Avoid "pretty" debug
pub struct NoPretty<T>(pub T);

impl<T> fmt::Debug for NoPretty<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// Format all iterator elements lazily, separated by `sep`.
///
/// The format value can only be formatted once, after that the iterator is
/// exhausted.
///
/// See [`.format()`](../trait.Itertools.html#method.format)
/// for more information.
#[derive(Clone)]
pub struct Format<'a, I> {
    sep: &'a str,
    /// Format uses interior mutability because Display::fmt takes &self.
    inner: RefCell<Option<I>>,
}

pub trait IterFormatExt: Iterator {
    fn format(self, separator: &str) -> Format<Self>
    where
        Self: Sized,
    {
        Format {
            sep: separator,
            inner: RefCell::new(Some(self)),
        }
    }
}

impl<I> IterFormatExt for I where I: Iterator {}

impl<I> Format<'_, I>
where
    I: Iterator,
{
    fn format<F>(&self, f: &mut fmt::Formatter, mut cb: F) -> fmt::Result
    where
        F: FnMut(&I::Item, &mut fmt::Formatter) -> fmt::Result,
    {
        let mut iter = match self.inner.borrow_mut().take() {
            Some(t) => t,
            None => panic!("Format: was already formatted once"),
        };

        if let Some(fst) = iter.next() {
            cb(&fst, f)?;
            for elt in iter {
                if !self.sep.is_empty() {
                    f.write_str(self.sep)?;
                }
                cb(&elt, f)?;
            }
        }
        Ok(())
    }
}

macro_rules! impl_format {
    ($($fmt_trait:ident)*) => {
        $(
            impl<'a, I> fmt::$fmt_trait for Format<'a, I>
                where I: Iterator,
                      I::Item: fmt::$fmt_trait,
            {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    self.format(f, fmt::$fmt_trait::fmt)
                }
            }
        )*
    }
}

impl_format!(Debug);
