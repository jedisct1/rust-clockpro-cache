#![feature(test)]
extern crate test;

#[macro_use]
extern crate bitflags;

use unsafe_unwrap::UnsafeUnwrap;

use crate::token_ring::{Token, TokenRing};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;

bitflags! {
    struct NodeType: u8 {
        const EMPTY     = 0b00001;
        const HOT       = 0b00010;
        const COLD      = 0b00100;
        const TEST      = 0b01000;
        const MASK      = Self::EMPTY.bits | Self::HOT.bits | Self::COLD.bits | Self::TEST.bits;
        const REFERENCE = 0b10000;
    }
}

struct Node<K, V> {
    key: K,
    value: Option<V>,
    node_type: NodeType,
    phantom_k: PhantomData<K>,
}

pub struct ClockProCache<K, V> {
    capacity: usize,
    test_capacity: usize,
    cold_capacity: usize,
    map: HashMap<K, Token>,
    ring: TokenRing,
    slab: Vec<Option<Node<K, V>>>,
    hand_hot: Token,
    hand_cold: Token,
    hand_test: Token,
    count_hot: usize,
    count_cold: usize,
    count_test: usize,
    inserted: u64,
    evicted: u64,
    phantom_k: PhantomData<K>,
}

impl<K, V> ClockProCache<K, V>
where
    K: Eq + Hash + Clone,
{
    pub fn new(capacity: usize) -> Result<Self, &'static str> {
        Self::new_with_test_capacity(capacity, capacity)
    }

    pub fn new_with_test_capacity(
        capacity: usize,
        test_capacity: usize,
    ) -> Result<Self, &'static str> {
        if capacity < 3 {
            return Err("Cache size cannot be less than 3 entries");
        }
        let mut slab = Vec::with_capacity(capacity + test_capacity);
        for _ in 0..capacity + test_capacity {
            slab.push(None);
        }
        let cache = ClockProCache {
            capacity,
            test_capacity,
            cold_capacity: capacity,
            map: HashMap::with_capacity(capacity + test_capacity),
            ring: TokenRing::with_capacity(capacity + test_capacity),
            slab,
            hand_hot: 0,
            hand_cold: 0,
            hand_test: 0,
            count_hot: 0,
            count_cold: 0,
            count_test: 0,
            inserted: 0,
            evicted: 0,
            phantom_k: PhantomData,
        };
        Ok(cache)
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.count_cold + self.count_hot
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn recent_len(&self) -> usize {
        self.count_cold
    }

    #[inline]
    pub fn frequent_len(&self) -> usize {
        self.count_hot
    }

    #[inline]
    pub fn test_len(&self) -> usize {
        self.count_test
    }

    #[inline]
    pub fn inserted(&self) -> u64 {
        self.inserted
    }

    #[inline]
    pub fn evicted(&self) -> u64 {
        self.evicted
    }

    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash,
    {
        let token = match self.map.get(key) {
            None => return None,
            Some(&token) => token,
        };
        let node = unsafe { self.slab[token].as_mut().unsafe_unwrap() };
        node.value.as_ref()?;
        node.node_type.insert(NodeType::REFERENCE);
        Some(node.value.as_mut().unwrap())
    }

    pub fn get<Q: ?Sized>(&mut self, key: &Q) -> Option<&V>
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        let token = match self.map.get(key) {
            None => return None,
            Some(&token) => token,
        };
        let node = unsafe { self.slab[token].as_mut().unsafe_unwrap() };
        node.value.as_ref()?;
        node.node_type.insert(NodeType::REFERENCE);
        Some(node.value.as_ref().unwrap())
    }

    pub fn contains_key<Q: ?Sized>(&mut self, key: &Q) -> bool
    where
        Q: Hash + Eq,
        K: Borrow<Q>,
    {
        let token = match self.map.get(key) {
            None => return false,
            Some(&token) => token,
        };
        unsafe { self.slab[token].as_ref().unsafe_unwrap().value.is_some() }
    }

    pub fn insert(&mut self, key: K, value: V) -> bool {
        let token = match self.map.get(&key).cloned() {
            None => {
                let node = Node {
                    key,
                    value: Some(value),
                    node_type: NodeType::COLD,
                    phantom_k: PhantomData,
                };
                self.meta_add(node);
                self.count_cold += 1;
                self.inserted += 1;
                return true;
            }
            Some(token) => token,
        };
        {
            let mentry = unsafe { self.slab[token].as_mut().unsafe_unwrap() };
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
        let node = Node {
            key,
            value: Some(value),
            node_type: NodeType::HOT,
            phantom_k: PhantomData,
        };
        self.meta_add(node);
        self.count_hot += 1;
        true
    }

    fn meta_add(&mut self, node: Node<K, V>) {
        self.evict();
        let token = self.ring.insert_after(self.hand_hot);
        self.slab[token] = Some(node);
        self.map.insert(
            unsafe { self.slab[token].as_ref().unsafe_unwrap().key.clone() },
            token,
        );
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
            let mentry = unsafe { self.slab[self.hand_cold].as_mut().unsafe_unwrap() };
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
            let mentry = unsafe { self.slab[self.hand_hot].as_mut().unsafe_unwrap() };
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
        if unsafe {
            self.slab[self.hand_test]
                .as_ref()
                .unsafe_unwrap()
                .node_type
                .intersects(NodeType::TEST)
        } {
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
            let mentry = unsafe { self.slab[token].as_mut().unsafe_unwrap() };
            mentry.node_type.remove(NodeType::MASK);
            mentry.node_type.insert(NodeType::EMPTY);
            mentry.value = None;
            self.map.remove(&mentry.key);
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
    use self::slab::Slab;
    use slab;

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
            let slab = Slab::with_capacity(capacity);
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
            self.slab.remove(token);
        }

        pub fn insert_after(&mut self, to: Token) -> Token {
            if self.slab.is_empty() {
                let node = Node {
                    prev: TOKEN_THUMBSTONE,
                    next: TOKEN_THUMBSTONE,
                };
                let token = self.slab.insert(node);
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
                let token = self.slab.insert(node);
                self.slab[old_second].next = token;
                self.tail = token;
                token
            } else {
                let node = Node {
                    prev: old_second,
                    next: to,
                };
                let token = self.slab.insert(node);
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
    use rand::distributions::{Distribution, Normal, Uniform};
    use rand::thread_rng;
    use test::{black_box, Bencher};

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
            assert_eq!(cache.insert(i, i), true);
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
            assert_eq!(cache.insert(i, (vec![0u8; 12], i)), true);
        }
        for i in 0..2 {
            match cache.get(&i) {
                None => {}
                Some(x) => assert_eq!(x.1, i),
            }
        }
    }

    #[bench]
    fn bench_sequence(b: &mut Bencher) {
        let mut cache: ClockProCache<u64, u64> = ClockProCache::new(68).unwrap();
        b.iter(|| {
            for i in 1..1000 {
                let n = i % 100;
                black_box(cache.insert(n, n));
            }
        });
        b.iter(|| {
            for i in 1..1000 {
                let n = i % 100;
                black_box(cache.get(&n));
            }
        });
    }

    #[bench]
    fn bench_composite(b: &mut Bencher) {
        let mut cache: ClockProCache<u64, (Vec<u8>, u64)> = ClockProCache::new(68).unwrap();
        let mut rng = thread_rng();
        let uniform = Uniform::new(0, 100);
        let mut rand_iter = uniform.sample_iter(&mut rng);
        b.iter(|| {
            for _ in 1..1000 {
                let n = rand_iter.next().unwrap();
                black_box(cache.insert(n, (vec![0u8; 12], n)));
            }
        });
        b.iter(|| {
            for _ in 1..1000 {
                let n = rand_iter.next().unwrap();
                black_box(cache.get(&n));
            }
        });
    }

    #[bench]
    fn bench_composite_normal(b: &mut Bencher) {
        // The cache size is ~ 1x sigma (stddev) to retain roughly >68% of records
        const SIGMA: f64 = 50.0 / 3.0;
        let mut cache: ClockProCache<u64, (Vec<u8>, u64)> =
            ClockProCache::new(SIGMA as usize).unwrap();

        // This should roughly cover all elements (within 3-sigma)
        let mut rng = thread_rng();
        let normal = Normal::new(50.0, SIGMA);
        let mut rand_iter = normal.sample_iter(&mut rng).map(|x| (x as u64) % 100);
        b.iter(|| {
            for _ in 1..1000 {
                let n = rand_iter.next().unwrap();
                black_box(cache.insert(n, (vec![0u8; 12], n)));
            }
        });
        b.iter(|| {
            for _ in 1..1000 {
                let n = rand_iter.next().unwrap();
                black_box(cache.get(&n));
            }
        });
    }
}
