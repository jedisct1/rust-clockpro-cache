#[macro_use]
extern crate bitflags;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem;
use token_ring::{Token, TokenRing};

bitflags! {
    flags NodeType: u8 {
        const NODETYPE_EMPTY     = 0b00001,
        const NODETYPE_HOT       = 0b00010,
        const NODETYPE_COLD      = 0b00100,
        const NODETYPE_TEST      = 0b01000,
        const NODETYPE_MASK      =
        NODETYPE_EMPTY.bits | NODETYPE_HOT.bits | NODETYPE_COLD.bits | NODETYPE_TEST.bits,
        const NODETYPE_REFERENCE = 0b10000
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
    map: HashMap<KeyRef<K>, Token>,
    ring: TokenRing,
    slab: Vec<Node<K, V>>,
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
    where K: Eq + Hash
{
    pub fn new(capacity: usize) -> Result<Self, &'static str> {
        Self::new_with_test_capacity(capacity, capacity)
    }

    pub fn new_with_test_capacity(capacity: usize,
                                  test_capacity: usize)
                                  -> Result<Self, &'static str> {
        if capacity < 3 {
            return Err("Cache size cannot be less than 3 entries");
        }
        let mut slab = Vec::with_capacity(capacity + test_capacity);
        unsafe {
            slab.set_len(capacity + test_capacity);
        }
        let cache = ClockProCache {
            capacity: capacity,
            test_capacity: test_capacity,
            cold_capacity: capacity,
            map: HashMap::with_capacity(capacity + test_capacity),
            ring: TokenRing::with_capacity(capacity + test_capacity),
            slab: slab,
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
    pub fn recent_len(&self) -> usize {
        self.count_hot
    }

    #[inline]
    pub fn frequent_len(&self) -> usize {
        self.count_cold
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
        where K: Borrow<Q>,
              Q: Eq + Hash
    {
        let token = match self.map.get(Qey::from_ref(key)) {
            None => return None,
            Some(&token) => token,
        };
        let node = &mut self.slab[token];
        if node.value.is_none() {
            return None;
        }
        node.node_type.insert(NODETYPE_REFERENCE);
        Some(node.value.as_mut().unwrap())
    }

    pub fn get<Q: ?Sized>(&mut self, key: &Q) -> Option<&V>
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        let token = match self.map.get(Qey::from_ref(key)) {
            None => return None,
            Some(&token) => token,
        };
        let node = &mut self.slab[token];
        if node.value.is_none() {
            return None;
        }
        node.node_type.insert(NODETYPE_REFERENCE);
        Some(node.value.as_ref().unwrap())
    }

    pub fn contains_key<Q: ?Sized>(&mut self, key: &Q) -> bool
        where Q: Hash + Eq,
              K: Borrow<Q>
    {
        let token = match self.map.get(Qey::from_ref(key)) {
            None => return false,
            Some(&token) => token,
        };
        self.slab[token].value.is_some()
    }

    pub fn insert(&mut self, key: K, value: V) -> bool {
        let token = match self.map.get(&KeyRef { k: &key }).cloned() {
            None => {
                let node = Node {
                    key: key,
                    value: Some(value),
                    node_type: NODETYPE_COLD,
                    phantom_k: PhantomData,
                };
                self.meta_add(node);
                self.count_cold += 1;
                self.inserted += 1;
                return false;
            }
            Some(token) => token,
        };
        {
            let mentry = &mut self.slab[token];
            if mentry.value.is_some() {
                mentry.value = Some(value);
                mentry.node_type.insert(NODETYPE_REFERENCE);
                return true;
            }
        }
        if self.cold_capacity < self.capacity {
            self.cold_capacity += 1;
        }
        self.count_test -= 1;
        self.meta_del(token);
        let node = Node {
            key: key,
            value: Some(value),
            node_type: NODETYPE_HOT,
            phantom_k: PhantomData,
        };
        self.meta_add(node);
        self.count_hot += 1;
        true
    }

    fn meta_add(&mut self, node: Node<K, V>) {
        self.evict();
        let token = self.ring.insert_after(self.hand_hot);
        self.slab[token] = node;
        self.map.insert(KeyRef { k: &self.slab[token].key }, token);
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
            let mentry = &mut self.slab[self.hand_cold];
            if mentry.node_type.intersects(NODETYPE_COLD) {
                if mentry.node_type.intersects(NODETYPE_REFERENCE) {
                    mentry.node_type = NODETYPE_HOT;
                    self.count_cold -= 1;
                    self.count_hot += 1;
                } else {
                    mentry.node_type.remove(NODETYPE_MASK);
                    mentry.node_type.insert(NODETYPE_TEST);
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
            let mentry = &mut self.slab[self.hand_hot];
            if mentry.node_type.intersects(NODETYPE_HOT) {
                if mentry.node_type.intersects(NODETYPE_REFERENCE) {
                    mentry.node_type.remove(NODETYPE_REFERENCE);
                } else {
                    mentry.node_type.remove(NODETYPE_MASK);
                    mentry.node_type.insert(NODETYPE_COLD);
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
        if self.slab[self.hand_test].node_type.intersects(NODETYPE_TEST) {
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
            let mentry = &mut self.slab[token];
            mentry.node_type.remove(NODETYPE_MASK);
            mentry.node_type.insert(NODETYPE_EMPTY);
            mentry.value = None;
            self.map.remove(Qey::from_ref(&mentry.key));
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
    where K: Send,
          V: Send
{
}

unsafe impl<K, V> Sync for ClockProCache<K, V>
    where K: Sync,
          V: Sync
{
}

struct KeyRef<K> {
    k: *const K,
}

impl<K: Hash> Hash for KeyRef<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        unsafe { (*self.k).hash(state) }
    }
}

impl<K: PartialEq> PartialEq for KeyRef<K> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { (*self.k).eq(&*other.k) }
    }
}

impl<K: Eq> Eq for KeyRef<K> {}

#[derive(Hash, PartialEq, Eq)]
struct Qey<Q: ?Sized>(Q);

impl<Q: ?Sized> Qey<Q> {
    fn from_ref(q: &Q) -> &Self {
        unsafe { mem::transmute(q) }
    }
}

impl<K, Q: ?Sized> Borrow<Qey<Q>> for KeyRef<K>
    where K: Borrow<Q>
{
    fn borrow(&self) -> &Qey<Q> {
        Qey::from_ref(unsafe { (*self.k).borrow() })
    }
}

mod token_ring {
    extern crate slab;

    use self::slab::Slab;

    pub type Token = usize;
    const TOKEN_THUMBSTONE: Token = !0;

    pub struct Node {
        next: Token,
        prev: Token,
    }

    pub struct TokenRing {
        head: Token,
        tail: Token,
        slab: Slab<Node, Token>,
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
                slab: slab,
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
                let token = self.slab.insert(node).ok().expect("Slab full");
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
                let token = self.slab.insert(node).ok().expect("Slab full");
                self.slab[old_second].next = token;
                self.tail = token;
                token
            } else {
                let node = Node {
                    prev: old_second,
                    next: to,
                };
                let token = self.slab.insert(node).ok().expect("Slab full");
                self.slab[old_second].next = token;
                self.slab[to].prev = token;
                token
            }
        }
    }
}

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
        assert_eq!(cache.insert(i, i), false);
    }
    for i in 0..2 {
        match cache.get(&i) {
            None => {}
            Some(x) => assert_eq!(*x, i),
        }
    }
}
