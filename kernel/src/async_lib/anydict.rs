use core::any::Any;

use alloc::{borrow::Cow, boxed::Box, collections::BTreeMap};

pub(super) enum AnyDictResult<T> {
    Ok(T),
    TypeError,
    None,
}

pub(super) struct AnyDict {
    dict: BTreeMap<Cow<'static, str>, Box<dyn Any>>,
}

impl AnyDict {
    pub(super) const fn new() -> Self {
        Self {
            dict: BTreeMap::new(),
        }
    }

    pub(super) fn insert<T>(&mut self, key: Cow<'static, str>, value: T)
    where
        T: Any,
    {
        self.dict.insert(key, Box::new(value));
    }

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

    pub(super) fn remove(&mut self, key: &str) -> Option<Box<dyn Any>> {
        self.dict.remove(key)
    }
}
