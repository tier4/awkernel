//! Dictionary mapping from string to any value.

use alloc::{borrow::Cow, collections::BTreeMap};
use core::any::Any;

#[cfg(not(feature = "std"))]
use alloc::{boxed::Box, vec::Vec};

/// Return value of `AnyDict`.
pub(super) enum AnyDictResult<T> {
    Ok(T),     // Found.
    TypeError, // Type of stored value and requested type are incompatible.
    None,      // Not found.
}

/// Dictionary from `Cow<'static, str>` to any value.
pub(super) struct AnyDict {
    dict: BTreeMap<Cow<'static, str>, Box<dyn Any + Send>>,
}

impl AnyDict {
    /// Create a new `AnyDict`.
    pub(super) const fn new() -> Self {
        Self {
            dict: BTreeMap::new(),
        }
    }

    pub(super) fn keys(&self) -> Vec<Cow<'static, str>> {
        self.dict.keys().cloned().collect()
    }

    /// Insert a key value pair.
    pub(super) fn insert<T>(&mut self, key: Cow<'static, str>, value: T)
    where
        T: Any + Send,
    {
        self.dict.insert(key, Box::new(value));
    }

    /// Get a value stored before.
    /// If there is no value of the key, `AnyDictResult::None` will be returned.
    /// If the types are incompatible, `AnyDictResult::TypeError` will be returned.
    pub(super) fn get<T>(&self, key: &str) -> AnyDictResult<&T>
    where
        T: Any,
    {
        if let Some(value) = self.dict.get(key) {
            if let Some(result) = value.as_ref().downcast_ref::<T>() {
                AnyDictResult::Ok(result)
            } else {
                AnyDictResult::TypeError
            }
        } else {
            AnyDictResult::None
        }
    }

    /// Get a value stored before.
    /// If there is no value of the key, `AnyDictResult::None` will be returned.
    /// If the types are incompatible, `AnyDictResult::TypeError` will be returned.
    pub(super) fn get_mut<T>(&mut self, key: &str) -> AnyDictResult<&mut T>
    where
        T: Any,
    {
        if let Some(value) = self.dict.get_mut(key) {
            if let Some(result) = value.as_mut().downcast_mut::<T>() {
                AnyDictResult::Ok(result)
            } else {
                AnyDictResult::TypeError
            }
        } else {
            AnyDictResult::None
        }
    }

    /// Remove the value mapped by `key`.
    pub(super) fn remove(&mut self, key: &str) -> Option<Box<dyn Any + Send>> {
        self.dict.remove(key)
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use super::*;

    #[test]
    fn test() {
        let mut dict = AnyDict::new();

        dict.insert("key1".into(), 10 as u64);
        dict.insert("key2".into(), "Hello".to_string());

        let AnyDictResult::Ok(value1) = dict.get::<u64>("key1".into()) else {
            panic!()
        };
        let AnyDictResult::Ok(value2) = dict.get::<String>("key2".into()) else {
            panic!()
        };

        assert_eq!(*value1, 10);
        assert_eq!(*value2, "Hello");

        assert!(matches!(
            dict.get::<u64>("key2".into()),
            AnyDictResult::TypeError
        ));

        assert!(matches!(
            dict.get::<String>("key1".into()),
            AnyDictResult::TypeError
        ));

        assert!(matches!(
            dict.get::<u64>("key2".into()),
            AnyDictResult::TypeError
        ));

        assert!(matches!(dict.get::<()>("key3".into()), AnyDictResult::None))
    }
}
