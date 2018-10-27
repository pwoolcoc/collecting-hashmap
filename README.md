# Collecting HashMap

This is a HashMap that stores all values as a Vec of values instead of a single value. So a `CollectingHashMap<K, V>`
is pretty much the same as a `HashMap<K, Vec<V>>` with some tweaks to the API to make this a bit easier to work with

