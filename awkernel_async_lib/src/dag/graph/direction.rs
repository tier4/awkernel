//! Direction enum for edge direction.
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

/// Index into the NodeIndex and EdgeIndex arrays
/// Edge direction.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Ord, Eq, Hash)]
#[repr(usize)]
pub enum Direction {
    /// An `Outgoing` edge is an outward edge *from* the current node.
    Outgoing = 0,
    /// An `Incoming` edge is an inbound edge *to* the current node.
    #[allow(dead_code)]
    Incoming = 1,
}

impl Direction {
    /// Return `0` for `Outgoing` and `1` for `Incoming`.
    #[inline]
    pub fn index(self) -> usize {
        (self as usize) & 0x1
    }
}
