use std::hash::Hash;

mod ranked;
mod linked;

pub use ranked::*;
pub use linked::*;

pub trait Heap<K, V> where K: Hash + Eq, V: PartialOrd {
    fn is_empty(&self) -> bool;
    fn size(&self) -> usize;
    fn push(&mut self, key: K, value: V);
    fn top(&self) -> Option<&K>;
    fn top_mut(&mut self) -> Option<&mut K>;
    fn pop(&mut self) -> Option<K>;
}

pub trait DecreaseKey<K, V>: Heap<K, V> where K: Hash + Eq, V: PartialOrd {
    fn update(&mut self, key: &K, value: V);
    fn delete(&mut self, key: &K) -> Option<K>;
}
