#![doc = include_str!("../README.md")]

#[macro_use]
extern crate bitflags;

use crate::token_ring::{Token, TokenRing};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;
use std::mem::MaybeUninit;

bitflags! {
    struct NodeType: u8 {
        const EMPTY     = 0b00001;
        const HOT       = 0b00010;
        const COLD      = 0b00100;
        const TEST      = 0b01000;
        const MASK      = Self::EMPTY.bits() | Self::HOT.bits() | Self::COLD.bits() | Self::TEST.bits();
        const REFERENCE = 0b10000;
    }
}

struct Node<K, V> {
    key: MaybeUninit<K>,
    value: Option<V>,
    node_type: NodeType,
}

impl<K, V> Default for Node<K, V> {
    fn default() -> Self {
        Node {
            key: MaybeUninit::uninit(),
            value: None,
            node_type: NodeType::EMPTY,
        }
    }
}

/// A CLOCK-Pro cache that maps keys to values.
pub struct ClockProCache<K, V> {
    capacity: usize,
    test_capacity: usize,
    cold_capacity: usize,
    map: HashMap<K, Token>,
    ring: TokenRing,
    nodes: Vec<Node<K, V>>,
    hand_hot: Token,
    hand_cold: Token,
    hand_test: Token,
    count_hot: usize,
    count_cold: usize,
    count_test: usize,
    inserted: u64,
    evicted: u64,
}

impl<K, V> ClockProCache<K, V>
where
    K: Eq + Hash + Clone,
{
    /// Create a new cache with the given capacity.
    pub fn new(capacity: usize) -> Result<Self, &'static str> {
        Self::new_with_test_capacity(capacity, capacity)
    }

    /// Create a new cache with the given value and test capacities.
    ///
    /// The test capacity is used for tracking recently evicted entries, so that they will
    /// be considered frequently used if they get reinserted.
    pub fn new_with_test_capacity(
        capacity: usize,
        test_capacity: usize,
    ) -> Result<Self, &'static str> {
        if capacity < 3 {
            return Err("Cache size cannot be less than 3 entries");
        }
        let mut nodes = Vec::with_capacity(capacity + test_capacity);
        nodes.resize_with(capacity + test_capacity, Node::default);
        let cache = ClockProCache {
            capacity,
            test_capacity,
            cold_capacity: capacity,
            map: HashMap::with_capacity(capacity + test_capacity),
            ring: TokenRing::with_capacity(capacity + test_capacity),
            nodes,
            hand_hot: 0,
            hand_cold: 0,
            hand_test: 0,
            count_hot: 0,
            count_cold: 0,
            count_test: 0,
            inserted: 0,
            evicted: 0,
        };
        Ok(cache)
    }

    /// Returns the number of cached values.
    #[inline]
    pub fn len(&self) -> usize {
        self.count_cold + self.count_hot
    }

    /// Returns `true` when no values are currently cached.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of recently inserted values.
    #[inline]
    pub fn recent_len(&self) -> usize {
        self.count_cold
    }

    /// Returns the number of frequently fetched or updated values.
    #[inline]
    pub fn frequent_len(&self) -> usize {
        self.count_hot
    }

    /// Returns the number of test entries.
    #[inline]
    pub fn test_len(&self) -> usize {
        self.count_test
    }

    /// Returns how many values have been inserted into the cache overall.
    #[inline]
    pub fn inserted(&self) -> u64 {
        self.inserted
    }

    /// Returns how many values have been evicted from the cache.
    #[inline]
    pub fn evicted(&self) -> u64 {
        self.evicted
    }

    /// Get a mutable reference to the value in the cache mapped to by `key`.
    ///
    /// If no value exists for `key`, this returns `None`.
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash,
    {
        let token = *self.map.get(key)?;
        let node = &mut self.nodes[token];
        let value = node.value.as_mut()?;
        node.node_type.insert(NodeType::REFERENCE);
        Some(value)
    }

    /// Get an immutable reference to the value in the cache mapped to by `key`.
    ///
    /// If no value exists for `key`, this returns `None`.
    pub fn get<Q: ?Sized>(&mut self, key: &Q) -> Option<&V>
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        let token = *self.map.get(key)?;
        let node = &mut self.nodes[token];
        let value = &node.value.as_ref()?;
        node.node_type.insert(NodeType::REFERENCE);
        Some(value)
    }

    /// Returns `true` if there is a value in the cache mapped to by `key`.
    pub fn contains_key<Q: ?Sized>(&mut self, key: &Q) -> bool
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        if let Some(&token) = self.map.get(key) {
            self.nodes[token].value.is_some()
        } else {
            false
        }
    }

    /// Map `key` to `value` in the cache, possibly evicting old entries.
    ///
    /// This method returns `true` when this is a new entry, and `false` if an existing entry was
    /// updated.
    pub fn insert(&mut self, key: K, value: V) -> bool {
        let token = match self.map.get(&key).cloned() {
            None => {
                self.meta_add(key, value, NodeType::COLD);
                self.count_cold += 1;
                self.inserted += 1;
                return true;
            }
            Some(token) => token,
        };
        {
            let mentry = &mut self.nodes[token];
            if mentry.value.is_some() {
                mentry.value = Some(value);
                mentry.node_type.insert(NodeType::REFERENCE);
                return false;
            }
        }
        if self.cold_capacity < self.capacity {
            self.cold_capacity += 1;
        }
        self.count_test -= 1;
        self.meta_del(token);
        self.meta_add(key, value, NodeType::HOT);
        self.count_hot += 1;
        true
    }

    /// Remove the cache entry mapped to by `key`.
    ///
    /// This method returns the value removed from the cache. If `key` did not map to any value,
    /// then this returns `None`.
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash,
    {
        let token = *self.map.get(key)?;
        let node = &mut self.nodes[token];
        let value = node.value.take();

        // The key is in map, so the node must be HOT or COLD
        if node.node_type.intersects(NodeType::HOT) {
            self.count_hot -= 1;
        } else if node.node_type.intersects(NodeType::COLD) {
            self.count_cold -= 1;
        }

        self.meta_del(token);
        value
    }

    fn meta_add(&mut self, key: K, value: V, node_type: NodeType) {
        self.evict();
        let token = self.ring.insert_after(self.hand_hot);
        self.nodes[token] = Node {
            key: MaybeUninit::new(key.clone()),
            value: Some(value),
            node_type,
        };
        self.map.insert(key, token);
        if self.hand_cold == self.hand_hot {
            self.hand_cold = self.ring.prev_for_token(self.hand_cold);
        }
    }

    fn evict(&mut self) {
        while self.count_hot + self.count_cold >= self.capacity {
            self.run_hand_cold();
        }
    }

    fn run_hand_cold(&mut self) {
        let mut run_hand_test = false;
        {
            let mentry = &mut self.nodes[self.hand_cold];
            if mentry.node_type.intersects(NodeType::COLD) {
                if mentry.node_type.intersects(NodeType::REFERENCE) {
                    mentry.node_type = NodeType::HOT;
                    self.count_cold -= 1;
                    self.count_hot += 1;
                } else {
                    mentry.node_type.remove(NodeType::MASK);
                    mentry.node_type.insert(NodeType::TEST);
                    mentry.value = None;
                    self.count_cold -= 1;
                    self.count_test += 1;
                    run_hand_test = true
                }
            }
        }
        if run_hand_test {
            while self.count_test > self.test_capacity {
                self.run_hand_test();
            }
        }
        self.hand_cold = self.ring.next_for_token(self.hand_cold);
        while self.count_hot > self.capacity - self.cold_capacity {
            self.run_hand_hot();
        }
    }

    fn run_hand_hot(&mut self) {
        if self.hand_hot == self.hand_test {
            self.run_hand_test();
        }
        {
            let mentry = &mut self.nodes[self.hand_hot];
            if mentry.node_type.intersects(NodeType::HOT) {
                if mentry.node_type.intersects(NodeType::REFERENCE) {
                    mentry.node_type.remove(NodeType::REFERENCE);
                } else {
                    mentry.node_type.remove(NodeType::MASK);
                    mentry.node_type.insert(NodeType::COLD);
                    self.count_hot -= 1;
                    self.count_cold += 1;
                }
            }
        }
        self.hand_hot = self.ring.next_for_token(self.hand_hot);
    }

    fn run_hand_test(&mut self) {
        if self.hand_test == self.hand_cold {
            self.run_hand_cold();
        }
        if self.nodes[self.hand_test]
            .node_type
            .intersects(NodeType::TEST)
        {
            let prev = self.ring.prev_for_token(self.hand_test);
            let hand_test = self.hand_test;
            self.meta_del(hand_test);
            self.hand_test = prev;
            self.count_test -= 1;
            if self.cold_capacity > 1 {
                self.cold_capacity -= 1;
            }
        }
        self.hand_test = self.ring.next_for_token(self.hand_test);
    }

    fn meta_del(&mut self, token: Token) {
        {
            let mentry = &mut self.nodes[token];
            mentry.node_type.remove(NodeType::MASK);
            mentry.node_type.insert(NodeType::EMPTY);
            mentry.value = None;
            self.map.remove(unsafe { mentry.key.assume_init_ref() });
        }
        if token == self.hand_hot {
            self.hand_hot = self.ring.prev_for_token(self.hand_hot);
        }
        if token == self.hand_cold {
            self.hand_cold = self.ring.prev_for_token(self.hand_cold);
        }
        if token == self.hand_test {
            self.hand_test = self.ring.prev_for_token(self.hand_test);
        }
        self.ring.remove(token);
        self.evicted += 1;
    }
}

unsafe impl<K, V> Send for ClockProCache<K, V>
where
    K: Send,
    V: Send,
{
}

unsafe impl<K, V> Sync for ClockProCache<K, V>
where
    K: Sync,
    V: Sync,
{
}

mod token_ring {
    use slabigator::Slab;

    pub type Token = usize;
    const TOKEN_THUMBSTONE: Token = !0;

    pub struct Node {
        next: Token,
        prev: Token,
    }

    pub struct TokenRing {
        head: Token,
        tail: Token,
        slab: Slab<Node>,
    }

    impl TokenRing {
        pub fn with_capacity(capacity: usize) -> Self {
            if capacity < 1 {
                panic!("A ring cannot have a capacity smaller than 1");
            }
            let slab = Slab::with_capacity(capacity).expect("requested capacity is too large");
            TokenRing {
                head: TOKEN_THUMBSTONE,
                tail: TOKEN_THUMBSTONE,
                slab,
            }
        }

        #[allow(dead_code)]
        #[inline]
        pub fn len(&self) -> usize {
            self.slab.len()
        }

        #[inline]
        pub fn next_for_token(&self, token: Token) -> Token {
            let next = self.slab[token].next;
            if next == TOKEN_THUMBSTONE {
                assert!(self.head != TOKEN_THUMBSTONE);
                self.head
            } else {
                next
            }
        }

        #[inline]
        pub fn prev_for_token(&self, token: Token) -> Token {
            let prev = self.slab[token].prev;
            if prev == TOKEN_THUMBSTONE {
                assert!(self.tail != TOKEN_THUMBSTONE);
                self.tail
            } else {
                prev
            }
        }

        pub fn remove(&mut self, token: Token) {
            let (prev, next) = (self.slab[token].prev, self.slab[token].next);
            if prev != TOKEN_THUMBSTONE {
                self.slab[prev].next = next;
            } else {
                self.head = next;
            }
            if next != TOKEN_THUMBSTONE {
                self.slab[next].prev = prev;
            } else {
                self.tail = prev;
            }
            self.slab[token].prev = TOKEN_THUMBSTONE;
            self.slab[token].next = TOKEN_THUMBSTONE;
            self.slab.remove(token).expect("removed token not in slab");
        }

        pub fn insert_after(&mut self, to: Token) -> Token {
            if self.slab.is_empty() {
                let node = Node {
                    prev: TOKEN_THUMBSTONE,
                    next: TOKEN_THUMBSTONE,
                };
                let token = self.slab.push_front(node).expect("over capacity");
                self.head = token;
                self.tail = token;
                return token;
            }
            let to_prev = self.slab[to].prev;
            let old_second = to_prev;
            if old_second == TOKEN_THUMBSTONE {
                let old_second = self.tail;
                let node = Node {
                    prev: old_second,
                    next: TOKEN_THUMBSTONE,
                };
                let token = self.slab.push_front(node).expect("over capacity");
                self.slab[old_second].next = token;
                self.tail = token;
                token
            } else {
                let node = Node {
                    prev: old_second,
                    next: to,
                };
                let token = self.slab.push_front(node).expect("over capacity");
                self.slab[old_second].next = token;
                self.slab[to].prev = token;
                token
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ClockProCache;

    #[test]
    fn test_cache() {
        let mut cache = ClockProCache::new(3).unwrap();
        cache.insert("testkey", "testvalue");
        assert!(cache.contains_key("testkey"));
        cache.insert("testkey2", "testvalue2");
        assert!(cache.contains_key("testkey2"));
        cache.insert("testkey3", "testvalue3");
        assert!(cache.contains_key("testkey3"));
        cache.insert("testkey4", "testvalue4");
        assert!(cache.contains_key("testkey4"));
        assert!(cache.contains_key("testkey3"));
        assert!(!cache.contains_key("testkey2"));
        cache.insert("testkey", "testvalue");
        assert!(cache.get_mut("testkey").is_some());
        assert!(cache.get_mut("testkey-nx").is_none());
    }

    #[test]
    fn test_recycle() {
        let mut cache: ClockProCache<u64, u64> = ClockProCache::new(3).unwrap();
        for i in 0..7 {
            assert!(cache.insert(i, i));
        }
        for i in 0..2 {
            match cache.get(&i) {
                None => {}
                Some(x) => assert_eq!(*x, i),
            }
        }
    }

    #[test]
    fn test_composite() {
        let mut cache: ClockProCache<u64, (Vec<u8>, u64)> = ClockProCache::new(3).unwrap();
        for i in 0..7 {
            assert!(cache.insert(i, (vec![0u8; 12], i)));
        }
        for i in 0..2 {
            match cache.get(&i) {
                None => {}
                Some(x) => assert_eq!(x.1, i),
            }
        }
    }

    #[test]
    fn test_remove() {
        let mut cache: ClockProCache<u64, u64> = ClockProCache::new(4).unwrap();
        for i in 0..4 {
            assert!(cache.insert(i, i));
        }

        assert_eq!(cache.remove(&2), Some(2));
        assert_eq!(cache.remove(&3), Some(3));
        assert_eq!(cache.remove(&3), None);

        for i in 0..4 {
            match i {
                2 | 3 => assert_eq!(cache.get(&i), None),
                _ => assert_eq!(*cache.get(&i).unwrap(), i),
            };
        }

        // Reinsert removed entries
        for i in 2..4 {
            assert!(cache.insert(i, i));
        }

        // Check that all entries still exist
        for i in 0..4 {
            assert_eq!(*cache.get(&i).unwrap(), i);
        }
    }

    #[test]
    fn test_length_and_counters() {
        let mut cache: ClockProCache<usize, usize> = ClockProCache::new(5).unwrap();

        // Cache starts out empty.
        assert_eq!(cache.is_empty(), true);

        for i in 1..=5 {
            // Cache length should increase with each new item.
            assert!(cache.insert(i, i));
            assert_eq!(cache.len(), i);
        }

        // Cache is no longer empty.
        assert_eq!(cache.is_empty(), false);
        assert_eq!(cache.inserted(), 5);
        assert_eq!(cache.frequent_len(), 0);
        assert_eq!(cache.recent_len(), 5);

        // Cache length should be capped at capacity.
        assert!(cache.insert(6, 6));
        assert!(cache.insert(7, 7));

        assert_eq!(cache.len(), 5);
        assert_eq!(cache.inserted(), 7);
        assert_eq!(cache.frequent_len(), 0);
        assert_eq!(cache.recent_len(), 5);

        // Reference the two recent values and insert new ones to run the hand
        // and make the REFERENCED nodes HOT.
        assert_eq!(cache.get(&6), Some(&6));
        assert_eq!(cache.get(&7), Some(&7));

        for i in 8..=15 {
            assert!(cache.insert(i, i));
        }

        // Both 6 and 7 should be HOT and not have been evicted.
        assert_eq!(cache.get(&6), Some(&6));
        assert_eq!(cache.get(&7), Some(&7));

        assert_eq!(cache.len(), 5);
        assert_eq!(cache.inserted(), 15);
        assert_eq!(cache.frequent_len(), 2);
        assert_eq!(cache.recent_len(), 3);
        assert_eq!(cache.test_len(), 5);

        // Removing 6 and 15 should decrement HOT and COLD counters.
        assert_eq!(cache.remove(&6), Some(6));
        assert_eq!(cache.remove(&15), Some(15));
        assert_eq!(cache.frequent_len(), 1);
        assert_eq!(cache.recent_len(), 2);
    }

    #[test]
    fn test_evicted_to_hot() {
        let mut cache: ClockProCache<usize, usize> =
            ClockProCache::new_with_test_capacity(3, 30).unwrap();

        // Insert test capacity items.
        for i in 0..30 {
            assert!(cache.insert(i, i));
        }

        assert_eq!(cache.frequent_len(), 0);
        assert_eq!(cache.recent_len(), 3);
        assert_eq!(cache.test_len(), 27);

        // 10 should be evicted but still have a TEST node.
        assert_eq!(cache.get(&10), None);

        // Inserting 0 again should replace the TEST node w/ a HOT one.
        assert!(cache.insert(10, 10));
        assert_eq!(cache.frequent_len(), 1);
        assert_eq!(cache.recent_len(), 2);
        assert_eq!(cache.test_len(), 27);
    }
}
