//! Collecting HashMap
//!
//! This is a HashMap that allows the user to store multiple `V` values for each `K` key. Currently
//! it is implemented by internally keeping a `HashMap<K, Vec<V>>` and forwarding most operations
//! to that `HashMap`. There area  few calls where it does more than just forward, in order to keep
//! the API as functionally similar to a regular `HashMap<K, V>` as possible. The main difference
//! is with the `insert` method. Since it won't replace the original value if you `insert` another
//! value for the same `K`, this `insert` returns nothing.
//!
//! The `get` and `get_mut` methods have the same signature as a regular `HashMap<K, V>`. Instead
//! of returning the whole underlying `Vec` for a key, `get` and `get_mut` both return a reference
//! to the first item in the `Vec`. In order to get a reference to the whole `Vec` for a key, use
//! `get_all` and `get_all_mut`.
//!
//! The `Entry` API operates on the entire underlying `Vec` for a key.
//!
//! # Examples
//!
//! ```rust
//! # extern crate collecting_hashmap;
//! use collecting_hashmap::CollectingHashMap;
//!
//! # fn main() -> Result<(), Box<::std::error::Error>> {
//! let mut map = CollectingHashMap::new();
//! map.insert("voltron", "black");
//! map.insert("voltron", "red");
//! map.insert("voltron", "green");
//! map.insert("voltron", "blue");
//! map.insert("voltron", "yellow");
//! assert_eq!(map.get_all("voltron"), Some(&vec!["black", "red", "green", "blue", "yellow"]));
//! #   Ok(())
//! # }
//! ```
//!
//! ```rust
//! # extern crate collecting_hashmap;
//! use collecting_hashmap::CollectingHashMap;
//!
//! # fn main() -> Result<(), Box<::std::error::Error>> {
//! let query_string = vec![
//!     ("q", "query1"),
//!     ("t", "0m2s"),
//!     ("q", "query2"),
//!     ("q", "query3"),
//! ];
//! let map = query_string.into_iter().collect::<CollectingHashMap<_, _>>();
//! assert_eq!(map.get_all("q"), Some(&vec!["query1", "query2", "query3"]));
//! #   Ok(())
//! # }
//! ```

use std::{
    borrow::Borrow,
    collections::hash_map::{Drain, Entry, HashMap, Iter, IterMut, Keys, RandomState, Values, ValuesMut},
    default::Default,
    hash::{BuildHasher, Hash},
    marker::PhantomData,
};

/// A hashmap that stores a vec of values for each key
pub struct CollectingHashMap<K, V, S=RandomState>
    where K: Hash + Eq,
          S: BuildHasher
{
    store: HashMap<K, Vec<V>, S>,
    _k: PhantomData<K>,
    _v: PhantomData<V>,
    _s: PhantomData<S>,
}

impl<K, V, S> Default for CollectingHashMap<K, V, S>
    where K: Hash + Eq,
          S: BuildHasher + Default
{
    fn default() -> CollectingHashMap<K, V, S> {
        CollectingHashMap {
            store: HashMap::with_hasher(Default::default()),
            _k: PhantomData,
            _v: PhantomData,
            _s: PhantomData,
        }
    }
}

impl<K, V> CollectingHashMap<K, V, RandomState>
    where K: Hash + Eq,
{
    /// Creates a new CollectingHashMap with the default Hasher
    pub fn new() -> CollectingHashMap<K, V, RandomState> {
        CollectingHashMap {
            store: HashMap::new(),
            .. Default::default()
        }
    }

    /// Creates a new CollectingHashMap with the given capacity
    pub fn with_capacity(capacity: usize) -> CollectingHashMap<K, V, RandomState> {
        CollectingHashMap {
            store: HashMap::with_capacity(capacity),
            .. Default::default()
        }
    }
}

impl<K, V, S> CollectingHashMap<K, V, S>
    where K: Hash + Eq,
          S: BuildHasher,
{
    /// Creates a new CollectingHashMap using the given HashMap for it's backing storage
    pub fn with_hashmap(h: HashMap<K, Vec<V>, S>) -> CollectingHashMap<K, V, S> {
        CollectingHashMap {
            store: h,
            _k: PhantomData,
            _v: PhantomData,
            _s: PhantomData,
        }
    }

    /// Inserts a value for the given key
    ///
    /// If the key is already present, this will append the value to the key's `Vec<V>`
    pub fn insert(&mut self, k: K, v: V) {
        if let Some(r) = self.store.get_mut(&k) {
            r.push(v);
        } else {
            self.store.insert(k, vec![v]);
        }
    }

    /// Retrieves a reference to a value for the given key
    ///
    /// If there is at least one value for the given key, this will return `&V` using the first
    /// element of `K`s `Vec<V>`
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Hash + Eq,
    {
        self.store.get(key).and_then(|r| r.get(0))
    }

    /// Retrieves a mutable reference to a value for the given key
    ///
    /// If there is at least one value for the given key, this will return `&mut V` using the first
    /// element of `K`s `Vec<V>`
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Hash + Eq,
    {
        self.store.get_mut(key).and_then(|r| r.get_mut(0))
    }

    /// Retrieves a reference to all values stored for the given key
    ///
    /// If there is at least one value present for the given key, this will return a reference to
    /// the `Vec<V>` for the key
    pub fn get_all<Q: ?Sized>(&self, key: &Q) -> Option<&Vec<V>>
        where K: Borrow<Q>,
              Q: Hash + Eq,
    {
        self.store.get(key)
    }

    /// Retrieves a mutable reference to all values stored for the given key
    ///
    /// If there is at least one value present for the given key, this will return a mutable
    /// reference to the `Vec<V>` for the key
    pub fn get_all_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut Vec<V>>
        where K: Borrow<Q>,
              Q: Hash + Eq,
    {
        self.store.get_mut(key)
    }

    /// Removes a set of values for the given key
    ///
    /// If there is a value present for the given key, this will remove all values from the
    /// underlying `HashMap` but will ONLY return the first element. To return the entire `Vec<V>`
    /// for the key, use `remove_all`
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Hash + Eq,
    {
        self.store.remove(key).map(|mut v| v.remove(0))
    }

    /// Removes a set of values for the given key
    ///
    /// If there is a value present for the given key, this will remove all values from the
    /// underlying `HashMap`, and return the `Vec<V>`
    pub fn remove_all<Q: ?Sized>(&mut self, key: &Q) -> Option<Vec<V>>
        where K: Borrow<Q>,
              Q: Hash + Eq,
    {
        self.store.remove(key)
    }

    // Delegate to the underlying hashmap

    /// The same as
    /// [HashMap::hasher](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.hasher)
    pub fn hasher(&self) -> &S {
        self.store.hasher()
    }

    /// The same as
    /// [HashMap::capacity](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.capacity)
    pub fn capacity(&self) -> usize {
        self.store.capacity()
    }

    /// The same as
    /// [HashMap::is_empty](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.is_empty)
    pub fn is_empty(&self) -> bool {
        self.store.is_empty()
    }

    /// The same as
    /// [HashMap::reserve](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve)
    pub fn reserve(&mut self, amt: usize) {
        self.store.reserve(amt)
    }

    /// The same as
    /// [HashMap::shrink_to_fit](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.shrink_to_fit)
    pub fn shrink_to_fit(&mut self) {
        self.store.shrink_to_fit()
    }

    /// The same as
    /// [HashMap::keys](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.keys)
    pub fn keys(&self) -> Keys<K, Vec<V>> {
        self.store.keys()
    }

    /// The same as
    /// [HashMap::values](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.values)
    pub fn values(&self) -> Values<K, Vec<V>> {
        self.store.values()
    }

    /// The same as
    /// [HashMap::values_mut](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.values_mut)
    pub fn values_mut(&mut self) -> ValuesMut<K, Vec<V>> {
        self.store.values_mut()
    }

    /// The same as
    /// [HashMap::iter](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.iter)
    pub fn iter(&self) -> Iter<K, Vec<V>> {
        self.store.iter()
    }

    /// The same as
    /// [HashMap::iter_mut](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.iter_mut)
    pub fn iter_mut(&mut self) -> IterMut<K, Vec<V>> {
        self.store.iter_mut()
    }

    /// The same as
    /// [HashMap::entry](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.entry)
    pub fn entry(&mut self, key: K) -> Entry<K, Vec<V>> {
        self.store.entry(key)
    }

    /// The same as
    /// [HashMap::len](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.len)
    pub fn len(&self) -> usize {
        self.store.len()
    }

    /// The same as
    /// [HashMap::drain](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.drain)
    pub fn drain(&mut self) -> Drain<K, Vec<V>> {
        self.store.drain()
    }

    /// The same as
    /// [HashMap::clear](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.clear)
    pub fn clear(&mut self) {
        self.store.clear()
    }

    /// The same as
    /// [HashMap::contains_key](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.contains_key)
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
        where K: Borrow<Q>,
              Q: Hash + Eq
    {
        self.store.contains_key(k)
    }

    /// The same as
    /// [HashMap::remove_entry](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.remove_entry)
    pub fn remove_entry<Q: ?Sized>(&mut self, key: &Q) -> Option<(K, Vec<V>)>
        where K: Borrow<Q>,
              Q: Hash + Eq,
    {
        self.store.remove_entry(key)
    }

    /// The same as
    /// [HashMap::retain](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.retain)
    pub fn retain<F>(&mut self, f: F)
        where F: FnMut(&K, &mut Vec<V>) -> bool,
    {
        self.store.retain(f)
    }
}

impl<K, V, S> ::std::iter::FromIterator<(K, V)> for CollectingHashMap<K, V, S>
    where K: Hash + Eq,
          S: BuildHasher + Default
{
    fn from_iter<T: IntoIterator<Item=(K, V)>>(iter: T) -> CollectingHashMap<K, V, S> {
        let map = HashMap::with_hasher(Default::default());
        let mut map = CollectingHashMap::with_hashmap(map);
        map.extend(iter);
        map
    }
}

impl<K, V, S> ::std::iter::Extend<(K, V)> for CollectingHashMap<K, V, S>
    where K: Hash + Eq,
          S: BuildHasher
{
    fn extend<T: IntoIterator<Item=(K, V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            (iter.size_hint().0 + 1) / 2
        };
        self.reserve(reserve);
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_and_get() {
        let mut h: CollectingHashMap<String, String> = CollectingHashMap::new();
        h.insert("foo".into(), "bar".into());
        h.insert("foo".into(), "baz".into());
        let r = h.get("foo");
        assert_eq!(Some(&"bar".to_string()), r);
    }

    #[test]
    fn insert_and_get_all() {
        let mut h = CollectingHashMap::new();
        h.insert("foo".to_string(), "bar".to_string());
        h.insert("foo".to_string(), "baz".to_string());
        let r = h.get_all("foo");
        assert_eq!(Some(&vec!["bar".to_string(), "baz".to_string()]), r);
    }

    #[test]
    fn insert_iter_of_tuples() {
        let data = vec![
            ("one", "two"),
            ("three", "four"),
            ("one", "five"),
        ];
        let map: CollectingHashMap<_, _> = data.into_iter().collect();

        assert_eq!(map.get_all("three"), Some(&vec!["four"]));
        assert_eq!(map.get_all("one"), Some(&vec!["two", "five"]));
    }
}

