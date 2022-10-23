use std::{
    hash::Hash,
    ptr::NonNull,
};
use std::marker::PhantomData;
use crate::{DecreaseKey, Heap, HeapPasses, HeapRank, HeapType};

type Link<K, P> = Option<NonNull<Node<K, P>>>;

struct Node<K: Hash + Eq, P: PartialOrd> {
    priority: P,
    key: K,
    left: Link<K, P>,
    next: Link<K, P>,
    parent:  Link<K, P>,
    is_root: bool,
}

impl<K: Hash + Eq, P: PartialOrd> Node<K, P> {
    pub fn new(key: K, priority: P) -> Self {
        Node {
            key,
            priority,
            left: None,
            next: None,
            parent: None,
            is_root: true,
        }
    }
}

/// dummy comment
pub struct LinkedRankPairingHeap<K: Hash + Eq, P: PartialOrd> {
    heap_rank: HeapRank,
    heap_type: HeapType,
    passes: HeapPasses,
    root: Link<K, P>,
    len: usize,
    _phantom_priority: PhantomData<P>,
    _phantom_key: PhantomData<K>,
}

// struct initialization
impl<K: Hash + Eq, P: PartialOrd> LinkedRankPairingHeap<K, P> {
    fn new(heap_type: HeapType, heap_rank: HeapRank, passes: HeapPasses) -> Self {
        LinkedRankPairingHeap {
            root: None,
            heap_rank,
            heap_type,
            passes,
            len: 0,
            _phantom_priority: PhantomData,
            _phantom_key: PhantomData,
        }
    }

    /// Initializes a max ([`HeapType::Max`]) heap using [`HeapRank::One`] and [`HeapPasses::Single`]
    ///
    /// ```rust
    /// use heapz::RankPairingHeap;
    ///
    /// let heap: RankPairingHeap<(usize, usize), i32> = RankPairingHeap::single_pass_max();
    /// ```
    pub fn single_pass_max() -> Self {
        Self::new(HeapType::Max, HeapRank::One, HeapPasses::Single)
    }

    /// Initializes a max ([`HeapType::Max`]) heap using [`HeapRank::Two`] and [`HeapPasses::Single`]
    ///
    /// ```rust
    /// use heapz::RankPairingHeap;
    ///
    /// let heap: RankPairingHeap<(usize, usize), i32> = RankPairingHeap::single_pass_max2();
    /// ```
    pub fn single_pass_max2() -> Self {
        Self::new(HeapType::Max, HeapRank::Two, HeapPasses::Single)
    }

    /// Initializes a min ([`HeapType::Min`]) heap using [`HeapRank::One`] and [`HeapPasses::Single`]
    ///
    /// ```rust
    /// use heapz::RankPairingHeap;
    ///
    /// let heap: RankPairingHeap<(usize, usize), i32> = RankPairingHeap::single_pass_min();
    /// ```
    pub fn single_pass_min() -> Self {
        Self::new(HeapType::Min, HeapRank::One, HeapPasses::Single)
    }

    /// Initializes a min ([`HeapType::Min`]) heap using [`HeapRank::Two`] and [`HeapPasses::Single`]
    ///
    /// ```rust
    /// use heapz::RankPairingHeap;
    ///
    /// let heap: RankPairingHeap<(usize, usize), i32> = RankPairingHeap::single_pass_min2();
    /// ```
    pub fn single_pass_min2() -> Self {
        Self::new(HeapType::Min, HeapRank::Two, HeapPasses::Single)
    }

    /// Initializes a min ([`HeapType::Max`]) heap using [`HeapRank::One`] and [`HeapPasses::Multi`]
    ///
    /// ```rust
    /// use heapz::RankPairingHeap;
    ///
    /// let heap: RankPairingHeap<(usize, usize), i32> = RankPairingHeap::multi_pass_max();
    /// ```
    pub fn multi_pass_max() -> Self {
        Self::new(HeapType::Max, HeapRank::One, HeapPasses::Multi)
    }

    /// Initializes a min ([`HeapType::Max`]) heap using [`HeapRank::Two`] and [`HeapPasses::Multi`]
    ///
    /// ```rust
    /// use heapz::RankPairingHeap;
    ///
    /// let heap: RankPairingHeap<(usize, usize), i32> = RankPairingHeap::multi_pass_max2();
    /// ```
    pub fn multi_pass_max2() -> Self {
        Self::new(HeapType::Max, HeapRank::Two, HeapPasses::Multi)
    }

    /// Initializes a min ([`HeapType::Min`]) heap using [`HeapRank::One`] and [`HeapPasses::Multi`]
    ///
    /// ```rust
    /// use heapz::RankPairingHeap;
    ///
    /// let heap: RankPairingHeap<(usize, usize), i32> = RankPairingHeap::multi_pass_min();
    /// ```
    pub fn multi_pass_min() -> Self {
        Self::new(HeapType::Min, HeapRank::One, HeapPasses::Multi)
    }

    /// Initializes a min ([`HeapType::Min`]) heap using [`HeapRank::Two`] and [`HeapPasses::Multi`]
    ///
    /// ```rust
    /// use heapz::RankPairingHeap;
    ///
    /// let heap: RankPairingHeap<(usize, usize), i32> = RankPairingHeap::multi_pass_max2();
    /// ```
    pub fn multi_pass_min2() -> Self {
        Self::new(HeapType::Min, HeapRank::Two, HeapPasses::Multi)
    }
}

// utility functions
impl<K: Hash + Eq, P: PartialOrd> LinkedRankPairingHeap<K, P> {
    fn create_node(key: K, priority: P) -> Link<K, P> {
        unsafe {
            Some(NonNull::new_unchecked(Box::into_raw(Box::new(Node::new(key, priority)))))
        }
    }

    fn compare(&self, node_a: NonNull<Node<K, P>>, node_b: NonNull<Node<K, P>>) -> bool {
        unsafe {
            if self.heap_type == HeapType::Max {
                (*node_a.as_ref()).priority > (*node_b.as_ref()).priority
            } else {
                (*node_a.as_ref()).priority > (*node_b.as_ref()).priority
            }
        }
    }

    fn add_node_to_roots(&self, node: Link<K, P>, root: Link<K, P>) -> Link<K, P> {
        if let Some(new_node) = node {
            unsafe {
                if let Some(root_node) = root {
                    if self.compare(new_node, root_node) {
                        (*new_node.as_ptr()).next = root;
                        (*new_node.as_ptr()).parent = (*root_node.as_ptr()).parent;
                        (*root_node.as_ptr()).parent = node;
                        node
                    } else {
                        (*new_node.as_ptr()).next = (*root_node.as_ptr()).next;
                        (*new_node.as_ptr()).parent = root;
                        (*root_node.as_ptr()).next = node;
                        root
                    }
                } else {
                    (*new_node.as_ptr()).next = node;
                    (*new_node.as_ptr()).parent = node;
                    node
                }
            }
        } else {
            None
        }
    }
}

impl<K: Hash + Eq, P: PartialOrd> Heap<K, P> for LinkedRankPairingHeap<K, P> {
    fn is_empty(&self) -> bool {
        todo!()
    }

    fn size(&self) -> usize {
        self.len
    }

    fn push(&mut self, key: K, priority: P) {
        self.root = self.add_node_to_roots(Self::create_node(key, priority), self.root);
        self.len += 1;
    }

    fn top(&self) -> Option<&K> {
        todo!()
    }

    fn top_mut(&mut self) -> Option<&mut K> {
        todo!()
    }

    fn pop(&mut self) -> Option<K> {
        todo!()
    }
}

impl<K: Hash + Eq, P: PartialOrd> DecreaseKey<K, P> for LinkedRankPairingHeap<K, P> {
    fn update(&mut self, key: &K, priority: P) {
        todo!()
    }

    fn delete(&mut self, key: &K) -> Option<K> {
        todo!()
    }
}