use std::{
    hash::Hash,
    ptr::NonNull,
    
};
use std::cmp::max;
use std::collections::HashMap;
use std::fmt::Debug;
use std::marker::PhantomData;
use crate::{utils::Bucket, DecreaseKey, Heap, HeapPasses, HeapRank, HeapType};

type Link<K, P> = Option<NonNull<Node<K, P>>>;

#[derive(Debug)]
struct Node<K: Hash + Eq + Clone + Debug, P: PartialOrd + Debug> {
    priority: P,
    key: K,
    left: Link<K, P>,
    next: Link<K, P>,
    parent: Link<K, P>,
    rank: i32,
    is_root: bool,
}

impl<K: Hash + Eq + Clone + Debug, P: PartialOrd + Debug> Node<K, P> {
    pub fn new(key: K, priority: P) -> Self {
        Node {
            key,
            priority,
            left: None,
            next: None,
            parent: None,
            is_root: true,
            rank: 0,
        }
    }
}

/// dummy comment
pub struct LinkedRankPairingHeap<K: Hash + Eq + Clone + Debug, P: PartialOrd + Debug> {
    heap_rank: HeapRank,
    heap_type: HeapType,
    passes: HeapPasses,
    root: Link<K, P>,
    keys: HashMap<K, Link<K, P>>,
    len: usize,
    _phantom_priority: PhantomData<P>,
    _phantom_key: PhantomData<K>,
}

impl<K: Hash + Eq + Clone + Debug, P: PartialOrd + Debug> Drop for LinkedRankPairingHeap<K, P> {
    fn drop(&mut self) {
        while let Some(_) = self.pop() { }
    }
}

// struct initialization
impl<K: Hash + Eq + Clone + Debug, P: PartialOrd + Debug> LinkedRankPairingHeap<K, P> {
    fn new(heap_type: HeapType, heap_rank: HeapRank, passes: HeapPasses) -> Self {
        LinkedRankPairingHeap {
            root: None,
            heap_rank,
            heap_type,
            passes,
            keys: HashMap::new(),
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


// Ranking
impl<K, P> LinkedRankPairingHeap<K, P>
    where
        K: Hash + Eq + Clone + Debug,
        P: PartialOrd + Debug,
{
    fn rank1(left: i32, next: i32) -> i32 {
        if left != next {
            max(left, next)
        } else {
            left + 1
        }
    }

    fn rank2(left: i32, next: i32) -> i32 {
        max(left, next) + (if (left - next).abs() > 1 {
            0
        } else {
            1
        })
    }

    fn format_list(mut list: Link<K, P>) -> String {
        let mut acc = vec![];
        let mut seen = HashMap::new();
        unsafe {
            while let Some(node) = list {
                let key = format!("{:?}", (*node.as_ptr()).key);
                let next= (*node.as_ptr()).next;
                if seen.contains_key(&key) {
                    list = None;
                } else {
                    seen.insert(key.clone(), true);
                    acc.push(key.clone());
                    list = next;
                }
            }
        }
        format!("{:?}", acc)
    }

    fn rank(&self, left: i32, next: i32) -> i32 {
        match self.heap_rank {
            HeapRank::One => Self::rank1(left, next),
            HeapRank::Two => Self::rank2(left, next),
        }
    }

    fn get_rank(&self, link: Link<K, P>) -> i32 {
        unsafe {
            link.map(|node| (*node.as_ptr()).rank)
                .unwrap_or(-1)
        }
    }

    fn rank_node(&self, link: Link<K, P>) -> i32 {
        link.map(|node| {
            let left_rank = self.get_rank(Self::get_left(link));
            let next_rank = if Self::is_root(link) {
                left_rank
            } else {
                self.get_rank(Self::get_next(link))
            };
            self.rank(left_rank, next_rank)
        }).unwrap_or(-1)
    }

    fn update_rank(&self, node: NonNull<Node<K, P>>) {
        unsafe {
            (*node.as_ptr()).rank = self.rank_node(Some(node));
        }
    }

    fn update_ranks(&self, mut link: Link<K, P>) {
        while let Some(node) = link {
            self.update_rank(node);
            if Self::is_root(link) {
                link = None;
            } else {
                link = Self::get_parent(link);
            }
        }
    }
}

// utility functions
impl<K: Hash + Eq + Clone + Debug, P: PartialOrd + Debug> LinkedRankPairingHeap<K, P> {
    fn create_node(key: K, priority: P) -> Link<K, P> {
        unsafe {
            Some(NonNull::new_unchecked(Box::into_raw(Box::new(Node::new(key, priority)))))
        }
    }

    fn unbox_node(node: NonNull<Node<K, P>>) -> Node<K, P> {
        unsafe {
            *Box::from_raw(node.as_ptr())
        }
    }

    fn get_parent(node: Link<K, P>) -> Link<K, P> {
        unsafe {
            node.map(|node| (*node.as_ptr()).parent).unwrap_or(None)
        }
    }

    fn get_next(node: Link<K, P>) -> Link<K, P> {
        unsafe {
            node.map(|node| (*node.as_ptr()).next).unwrap_or(None)
        }
    }

    fn get_left(node: Link<K, P>) -> Link<K, P> {
        unsafe {
            node.map(|node| (*node.as_ptr()).left).unwrap_or(None)
        }
    }

    fn is_root(node: Link<K, P>) -> bool {
        unsafe {
            node.map(|node| (*node.as_ptr()).is_root).unwrap_or(false)
        }
    }

    fn is_left(node: Link<K, P>) -> bool {
        unsafe {
            Self::get_parent(node)
                .map(| parent | (*parent.as_ptr()).left == node)
                .unwrap_or(false)
        }
    }

    fn set_priority(link: Link<K, P>, priority: P) {
        unsafe {
            link.map(|node| { (*node.as_ptr()).priority = priority; });
        }
    }

    fn set_next(link: Link<K, P>, next: Link<K, P>) {
        unsafe {
            link.map(|node| { (*node.as_ptr()).next = next; });
        }
    }

    fn set_parent(link: Link<K, P>, parent: Link<K, P>) {
        unsafe {
            link.map(|node| { (*node.as_ptr()).parent = parent; });
        }
    }

    fn set_left(link: Link<K, P>, left: Link<K, P>) {
        unsafe {
            link.map(|node| { (*node.as_ptr()).left = left; });
        }
    }

    fn set_is_root(node: NonNull<Node<K, P>>, is_root: bool) {
        unsafe {
           (*node.as_ptr()).is_root = is_root;
        }
    }

    fn link_next(parent: Link<K, P>, next: Link<K, P>) {
        Self::set_next(parent, next);
        Self::set_parent(next, parent);
    }

    fn link_left(parent: Link<K, P>, left: Link<K, P>) {
        Self::set_parent(left, parent);
        Self::set_left(parent, left);
        left.map(| node | Self::set_is_root(node, false));
    }

    fn compare(&self, node_a: NonNull<Node<K, P>>, node_b: NonNull<Node<K, P>>) -> bool {
        unsafe {
            if self.heap_type == HeapType::Max {
                (*node_a.as_ptr()).priority > (*node_b.as_ptr()).priority
            } else {
                (*node_a.as_ptr()).priority < (*node_b.as_ptr()).priority
            }
        }
    }

    fn can_update_priority(&self, link: &Link<K, P>, priority: &P) -> bool {
        link.map(| node | unsafe {
            if self.heap_type == HeapType::Max {
                priority > &(*node.as_ptr()).priority
            } else {
                priority < &(*node.as_ptr()).priority
            }
        }).unwrap_or(false)
    }

    fn concatenate_lists(head: Link<K, P>, tail: Link<K, P>, next_head: Link<K, P>) -> Link<K, P> {
        match (head.zip(tail), next_head) {
            (Some((_, _)), Some(_)) => {
                Self::set_parent(head, None);
                Self::set_next(tail, next_head);
                Self::set_parent(next_head, tail);
                head
            },
            (Some((_, _)), None) => {
                Self::set_parent(head, None);
                Self::set_next(tail, None);
                head
            },
            (None, Some(_)) => {
                Self::set_parent(next_head, None);
                next_head
            },
            _ => None
        }
    }

    fn link_nodes(&self, node_a: NonNull<Node<K, P>>, node_b: NonNull<Node<K, P>>) ->  NonNull<Node<K, P>> {
        let node_a_is_parent = self.compare(node_a, node_b);
        let root = if node_a_is_parent { node_a } else { node_b };
        let child = if node_a_is_parent { node_b } else { node_a };
        let left = Self::get_left(Some(root));
        Self::link_next(Some(child), left);
        Self::link_left(Some(root), Some(child));
        self.update_rank(child);
        self.update_rank(root);
        root
    }

    fn add_node_to_roots(&self, node: Link<K, P>, root: Link<K, P>) -> Link<K, P> {
        if let Some(new_node) = node {
            Self::set_is_root(new_node, true);
            if let Some(root_node) = root {
                Self::link_next(Self::get_parent(root), node);
                Self::link_next(node, root);
                if self.compare(new_node, root_node) {
                    node
                } else {
                    root
                }
            } else {
                Self::link_next(node, node);
                node
            }
        } else {
            None
        }
    }

    fn unlink_root(node: Link<K, P>) -> (Link<K, P>, Link<K, P>) {
        let next = Self::get_next(node);
        let parent = Self::get_parent(node);
        Self::set_next(node, None);
        Self::set_parent(node, None);
        if parent != node && next != node {
            Self::link_next(parent, next);
            (parent, next)
        } else {
            (None, None)
        }
    }

    fn unlink_tree(node: Link<K, P>) -> (Link<K, P>, Link<K, P>) {
        let parent = Self::get_parent(node);
        let next = Self::get_next(node);
        if Self::is_left(node) {
            Self::link_left(parent, next);
        } else {
            Self::link_next(parent, next);
        }
        (parent, next)
    }

    fn unlink_node(node: Link<K, P>) -> (Link<K, P>, Link<K, P>, Link<K, P>) {
        let (parent, next) = Self::unlink_root(node);
        let left = Self::get_left(node);
        Self::set_parent(left, None);
        Self::set_left(node, None);
        (parent, next, left)
    }

    fn multi_pass(&self, mut list: Link<K, P>) -> Link<K, P> {
        let mut bucket: Bucket<NonNull<Node<K, P>>> = Bucket::new(self.size());
        let mut root = None;
        while let Some(mut node) = list {
            let mut rank = self.get_rank(list);
            let (_, next) = Self::unlink_root(list);
            if let Some(matched) = bucket.remove(rank as usize) {
                let (_, next) = Self::unlink_root(Some(matched));
                if root == Some(matched) { root = next; }
                node = self.link_nodes(node, matched);
                rank = self.get_rank(Some(node));
            }
            list = if bucket.contains_key(rank as usize) {
                Self::link_next(Some(node), next);
                Some(node)
            } else {
                bucket.insert(rank as usize, node);
                root = self.add_node_to_roots(Some(node), root);
                next
            };
        }
        root
    }

    fn single_pass(&self, mut list: Link<K, P>) -> Link<K, P> {
        let mut bucket: Bucket<NonNull<Node<K, P>>> = Bucket::new(self.size());
        let mut root = None;
        while let Some(mut node) = list {
            let rank = self.get_rank(Some(node));
            let (_, next) = Self::unlink_root(Some(node));
            if let Some(matched) = bucket.remove(rank as usize) {
                let (parent, _) = Self::unlink_root(Some(matched));
                if root == Some(matched) { root = parent; }
                node = self.link_nodes(node, matched);
            } else {
                bucket.insert(rank as usize, node);
            }
            root = self.add_node_to_roots(Some(node), root);
            list = next;
        }
        root
    }

    fn heapify(&self, list: Link<K, P>) -> Link<K, P> {
        if self.passes == HeapPasses::Single {
            self.single_pass(list)
        } else {
            self.multi_pass(list)
        }
    }
}

impl<K: Hash + Eq + Clone + Debug, P: PartialOrd + Debug> Heap<K, P> for LinkedRankPairingHeap<K, P> {
    fn is_empty(&self) -> bool {
        self.len <= 0
    }

    fn size(&self) -> usize {
        self.len
    }

    fn push(&mut self, key: K, priority: P) {
        let node = Self::create_node(key.clone(), priority);
        self.keys.insert(key.clone(), node);
        self.root = self.add_node_to_roots(node, self.root);
        self.len += 1;
    }

    fn top(&self) -> Option<&K> {
        unsafe {
            self.root.map(|node| &(*node.as_ptr()).key)
        }
    }

    fn top_mut(&mut self) -> Option<&mut K> {
        unsafe {
            self.root.map(|node| &mut (*node.as_ptr()).key)
        }
    }

    fn pop(&mut self) -> Option<K> {
        self.root.map(| node | {
            let (parent, next, left) = Self::unlink_node(Some(node));
            let removed = Self::unbox_node(node);
            self.keys.remove(&removed.key);
            self.root = self.heapify(Self::concatenate_lists(next, parent, left));
            self.len -= 1;
            removed.key
        })
    }
}

impl<K: Hash + Eq + Clone + Debug, P: PartialOrd + Debug> DecreaseKey<K, P> for LinkedRankPairingHeap<K, P> {
    fn update(&mut self, key: &K, priority: P) {
        if let Some(node) = self.keys.get(key) {
            if self.can_update_priority(node, &priority) {
                Self::set_priority(*node, priority);
                if *node != self.root {
                    let (parent, _) = Self::unlink_tree(*node);
                    self.update_ranks(parent);
                    self.root = self.add_node_to_roots(*node, self.root);
                }
            }
        };
    }

    fn delete(&mut self, key: &K) -> Option<K> {
        if let Some(node) = self.keys.remove(key) {
            if !Self::is_root(node) {
                let (parent, _) = Self::unlink_tree(node);
                self.update_ranks(parent);
                self.add_node_to_roots(node, self.root);
            }
            self.root = node;
            self.pop()
        } else {
            None
        }
    }
}

#[cfg(test)]
mod add_node_to_roots {
    use crate::LinkedRankPairingHeap;

    #[test]
    fn adds_new_node_as_root_if_it_is_the_highest_priority_in_min_heap() {
        let highest_priority = 1;
        let nums = vec![highest_priority,5,3,4,8,9,6,7,2];
        let heap = LinkedRankPairingHeap::multi_pass_min();
        let root = nums
            .into_iter()
            .fold(None, | list, num | heap.add_node_to_roots(LinkedRankPairingHeap::create_node(num, num), list))
            .unwrap();
       unsafe { assert_eq!(highest_priority, (*root.as_ptr()).key) }
    }

    #[test]
    fn adds_new_node_as_root_if_it_is_the_highest_priority_in_max_heap() {
        let highest_priority = 10;
        let nums = vec![highest_priority,5,3,4,8,9,6,7,2];
        let heap = LinkedRankPairingHeap::multi_pass_max();
        let root = nums
            .into_iter()
            .fold(None, | list, num | heap.add_node_to_roots(LinkedRankPairingHeap::create_node(num, num), list))
            .unwrap();
       unsafe { assert_eq!(highest_priority, (*root.as_ptr()).key) }
    }

    #[test]
    fn leaves_the_root_as_the_root_if_it_is_higher_priority_than_the_new_node() {
        let highest_priority = 10;
        let mut nums = vec![highest_priority,5,3,4,8,9,6,7,2];
        let len = nums.len();
        let mut comparison = vec![];
        let heap = LinkedRankPairingHeap::multi_pass_max();
        let mut root = nums
            .iter()
            .fold(None, | list, num | heap.add_node_to_roots(LinkedRankPairingHeap::create_node(*num, *num), list));
        for _ in 0..len {
            unsafe {
                let node = root.unwrap();
                comparison.push((*node.as_ptr()).key);
                root = (*node.as_ptr()).next;
            }
        }
        comparison.sort();
        nums.sort();
        assert_eq!(nums, comparison);
    }
}

#[cfg(test)]
mod concatenate_lists {
    use crate::LinkedRankPairingHeap;

    #[test]
    fn removes_the_parent_from_the_head_of_the_lists() {
        let head = LinkedRankPairingHeap::create_node(1, 1);
        let node = LinkedRankPairingHeap::create_node(2, 2);
        let tail = LinkedRankPairingHeap::create_node(3, 3);
        unsafe {
            (*head.unwrap().as_ptr()).next = node;
            (*head.unwrap().as_ptr()).parent = tail;
            (*node.unwrap().as_ptr()).next = tail;
            (*node.unwrap().as_ptr()).parent = head;
            (*tail.unwrap().as_ptr()).next = head;
            (*tail.unwrap().as_ptr()).parent = node;
        }
        let list = LinkedRankPairingHeap::concatenate_lists(head, tail, None);
        unsafe {
            assert_eq!((*(list.unwrap()).as_ptr()).parent, None);
        }
    }

    #[test]
    fn removes_next_from_the_tail_of_the_list() {
        let head = LinkedRankPairingHeap::create_node(1, 1);
        let node = LinkedRankPairingHeap::create_node(2, 2);
        let tail = LinkedRankPairingHeap::create_node(3, 3);
        unsafe {
            (*head.unwrap().as_ptr()).next = node;
            (*head.unwrap().as_ptr()).parent = tail;
            (*node.unwrap().as_ptr()).next = tail;
            (*node.unwrap().as_ptr()).parent = head;
            (*tail.unwrap().as_ptr()).next = head;
            (*tail.unwrap().as_ptr()).parent = node;
        }
        LinkedRankPairingHeap::concatenate_lists(head, tail, None);
        unsafe {
            assert_eq!((*(tail.unwrap()).as_ptr()).next, None);
        }
    }

    #[test]
    fn joins_two_lists_into_a_single_list() {
        let head_1 = LinkedRankPairingHeap::create_node(1, 1);
        let node_1 = LinkedRankPairingHeap::create_node(2, 2);
        let tail_1 = LinkedRankPairingHeap::create_node(3, 3);
        let head_2 = LinkedRankPairingHeap::create_node(4, 4);
        let node_2 = LinkedRankPairingHeap::create_node(5, 5);
        let tail_2 = LinkedRankPairingHeap::create_node(6, 6);
        unsafe {
            (*head_1.unwrap().as_ptr()).next = node_1;
            (*head_1.unwrap().as_ptr()).parent = tail_1;
            (*node_1.unwrap().as_ptr()).next = tail_1;
            (*node_1.unwrap().as_ptr()).parent = head_1;
            (*tail_1.unwrap().as_ptr()).next = head_1;
            (*tail_1.unwrap().as_ptr()).parent = node_1;
            (*head_2.unwrap().as_ptr()).next = node_2;
            (*node_2.unwrap().as_ptr()).next = tail_2;
            (*node_2.unwrap().as_ptr()).parent = head_2;
            (*tail_2.unwrap().as_ptr()).parent = node_2;
        };
        let mut list = LinkedRankPairingHeap::concatenate_lists(head_1, tail_1, head_2);
        let mut result = vec![];
        unsafe {
            while let Some(node) = list {
                result.push((*node.as_ptr()).key);
                list = (*node.as_ptr()).next;
            }
        }
        assert_eq!(result, vec![1, 2, 3, 4, 5, 6]);
    }
}

#[cfg(test)]
mod link_nodes {
    use crate::LinkedRankPairingHeap;

    #[test]
    fn makes_the_highest_priority_node_the_root() {
        let node_1 = LinkedRankPairingHeap::create_node(1, 1);
        let node_2 = LinkedRankPairingHeap::create_node(2, 2);
        let node_3 = LinkedRankPairingHeap::create_node(3, 3);
        let heap = LinkedRankPairingHeap::multi_pass_max();
        unsafe {
            (*(node_3.unwrap()).as_ptr()).left = node_1;
            let root = heap.link_nodes(node_2.unwrap(), node_3.unwrap());
            assert_eq!(Some(root), node_3);
        }
    }

    #[test]
    fn sets_the_lower_priority_node_as_the_left_child_of_the_root() {
        let node_1 = LinkedRankPairingHeap::create_node(1, 1);
        let node_2 = LinkedRankPairingHeap::create_node(2, 2);
        let node_3 = LinkedRankPairingHeap::create_node(3, 3);
        let heap = LinkedRankPairingHeap::multi_pass_max();
        unsafe {
            (*(node_3.unwrap()).as_ptr()).left = node_1;
            let root = heap.link_nodes(node_2.unwrap(), node_3.unwrap());
            assert_eq!((*root.as_ptr()).left, node_2);
        }
    }

    #[test]
    fn sets_the_left_child_of_the_root_as_the_next_of_its_new_left_child() {
        let node_1 = LinkedRankPairingHeap::create_node(1, 1);
        let node_2 = LinkedRankPairingHeap::create_node(2, 2);
        let node_3 = LinkedRankPairingHeap::create_node(3, 3);
        let heap = LinkedRankPairingHeap::multi_pass_max();
        unsafe {
            (*(node_3.unwrap()).as_ptr()).left = node_1;
            let _ = heap.link_nodes(node_2.unwrap(), node_3.unwrap());
            assert_eq!((*(node_2.unwrap()).as_ptr()).next, node_1);
        }
    }

    #[test]
    fn updates_the_rank_of_the_child_node() {
        let node_1 = LinkedRankPairingHeap::create_node(1, 1);
        let node_2 = LinkedRankPairingHeap::create_node(2, 2);
        let node_3 = LinkedRankPairingHeap::create_node(3, 3);
        let heap = LinkedRankPairingHeap::multi_pass_max();
        unsafe {
            (*(node_3.unwrap()).as_ptr()).left = node_1;
            let _ = heap.link_nodes(node_2.unwrap(), node_3.unwrap());
            assert_eq!((*(node_2.unwrap()).as_ptr()).rank, 0);
        }
    }

    #[test]
    fn updates_the_rank_of_the_root_node() {
        let node_1 = LinkedRankPairingHeap::create_node(1, 1);
        let node_2 = LinkedRankPairingHeap::create_node(2, 2);
        let node_3 = LinkedRankPairingHeap::create_node(3, 3);
        let heap = LinkedRankPairingHeap::multi_pass_max();
        unsafe {
            (*(node_3.unwrap()).as_ptr()).left = node_1;
            let root = heap.link_nodes(node_2.unwrap(), node_3.unwrap());
            assert_eq!((*root.as_ptr()).rank, 1);
        }
    }

    #[test]
    fn updates_the_rank_of_the_root_node_to_2_when_there_is_a_full_tree() {
        let node_1 = LinkedRankPairingHeap::create_node(1, 1);
        let node_2 = LinkedRankPairingHeap::create_node(2, 2);
        let node_3 = LinkedRankPairingHeap::create_node(3, 3);
        let node_4 = LinkedRankPairingHeap::create_node(-1, -1);
        let heap = LinkedRankPairingHeap::multi_pass_max();
        unsafe {
            (*(node_3.unwrap()).as_ptr()).left = node_1;
            (*(node_2.unwrap()).as_ptr()).left = node_4;
            let root = heap.link_nodes(node_2.unwrap(), node_3.unwrap());
            assert_eq!((*root.as_ptr()).rank, 2);
        }
    }
}

#[cfg(test)]
mod unlink_root {
    use crate::LinkedRankPairingHeap;

    #[test]
    fn removes_the_parent_node() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let _ = LinkedRankPairingHeap::unlink_root(node);
            assert_eq!((*n.as_ptr()).parent, None);
        }
    }

    #[test]
    fn removes_the_next_node() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let _ = LinkedRankPairingHeap::unlink_root(node);
            assert_eq!((*n.as_ptr()).next, None);
        }
    }

    #[test]
    fn returns_the_parent_node_if_not_linked_to_self() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let (returned_parent, _) = LinkedRankPairingHeap::unlink_root(node);
            assert_eq!(returned_parent, parent);
        }
    }

    #[test]
    fn returns_the_next_node_if_not_linked_to_self() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let (_, returned_next) = LinkedRankPairingHeap::unlink_root(node);
            assert_eq!(returned_next, next);
        }
    }

    #[test]
    fn links_the_parent_and_next_node_if_the_target_is_not_linked_to_itself() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let _ = LinkedRankPairingHeap::unlink_root(node);
            assert_eq!((*(parent.unwrap()).as_ptr()).next, next);
            assert_eq!((*(next.unwrap()).as_ptr()).parent, parent);
        }
    }

    #[test]
    fn will_not_link_a_node_back_to_itself() {
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = node;
            (*n.as_ptr()).parent = node;
            (*n.as_ptr()).left = left;
            let _ = LinkedRankPairingHeap::unlink_root(node);
            assert_eq!((*n.as_ptr()).parent, None);
            assert_eq!((*n.as_ptr()).next, None);
        }
    }

    #[test]
    fn will_not_return_a_parent_if_linked_to_itself() {
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = node;
            (*n.as_ptr()).parent = node;
            (*n.as_ptr()).left = left;
            let (returned_parent, _) = LinkedRankPairingHeap::unlink_root(node);
            assert_eq!(returned_parent, None);
        }
    }

    #[test]
    fn will_not_return_next_if_linked_to_itself() {
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = node;
            (*n.as_ptr()).parent = node;
            (*n.as_ptr()).left = left;
            let (_, returned_next) = LinkedRankPairingHeap::unlink_root(node);
            assert_eq!(returned_next, None);
        }
    }

    #[test]
    fn does_not_change_the_left_node() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let _ = LinkedRankPairingHeap::unlink_root(node);
            assert_eq!((*n.as_ptr()).left, left);
        }
    }
}

#[cfg(test)]
mod unlink_node {
    use crate::LinkedRankPairingHeap;

    #[test]
    fn removes_the_parent_node() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let _ = LinkedRankPairingHeap::unlink_node(node);
            assert_eq!((*n.as_ptr()).parent, None);
        }
    }

    #[test]
    fn removes_the_next_node() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let _ = LinkedRankPairingHeap::unlink_node(node);
            assert_eq!((*n.as_ptr()).next, None);
        }
    }

    #[test]
    fn returns_the_parent_node_if_not_linked_to_self() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let (returned_parent, _, _) = LinkedRankPairingHeap::unlink_node(node);
            assert_eq!(returned_parent, parent);
        }
    }

    #[test]
    fn returns_the_next_node_if_not_linked_to_self() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let (_, returned_next, _) = LinkedRankPairingHeap::unlink_node(node);
            assert_eq!(returned_next, next);
        }
    }

    #[test]
    fn links_the_parent_and_next_node_if_the_target_is_not_linked_to_itself() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let _ = LinkedRankPairingHeap::unlink_node(node);
            assert_eq!((*(parent.unwrap()).as_ptr()).next, next);
            assert_eq!((*(next.unwrap()).as_ptr()).parent, parent);
        }
    }

    #[test]
    fn will_not_link_a_node_back_to_itself() {
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = node;
            (*n.as_ptr()).parent = node;
            (*n.as_ptr()).left = left;
            let _ = LinkedRankPairingHeap::unlink_node(node);
            assert_eq!((*n.as_ptr()).parent, None);
            assert_eq!((*n.as_ptr()).next, None);
        }
    }

    #[test]
    fn will_not_return_a_parent_if_linked_to_itself() {
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = node;
            (*n.as_ptr()).parent = node;
            (*n.as_ptr()).left = left;
            let (returned_parent, _, _) = LinkedRankPairingHeap::unlink_node(node);
            assert_eq!(returned_parent, None);
        }
    }

    #[test]
    fn will_not_return_next_if_linked_to_itself() {
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = node;
            (*n.as_ptr()).parent = node;
            (*n.as_ptr()).left = left;
            let (_, returned_next, _) = LinkedRankPairingHeap::unlink_node(node);
            assert_eq!(returned_next, None);
        }
    }

    #[test]
    fn removes_the_left_node() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let _ = LinkedRankPairingHeap::unlink_node(node);
            assert_eq!((*n.as_ptr()).left, None);
        }
    }

    #[test]
    fn removes_the_left_nodes_parent() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            let l = left.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            (*l.as_ptr()).parent = node;
            assert_eq!((*l.as_ptr()).parent, node);
            let _ = LinkedRankPairingHeap::unlink_node(node);
            assert_eq!((*l.as_ptr()).parent, None);
        }
    }

    #[test]
    fn returns_the_left_node() {
        let parent = LinkedRankPairingHeap::create_node(1, 1);
        let next = LinkedRankPairingHeap::create_node(2, 2);
        let node = LinkedRankPairingHeap::create_node(3, 3);
        let left = LinkedRankPairingHeap::create_node(4, 4);
        unsafe {
            let n = node.unwrap();
            (*n.as_ptr()).next = next;
            (*n.as_ptr()).parent = parent;
            (*n.as_ptr()).left = left;
            let (_, _, returned_left) = LinkedRankPairingHeap::unlink_node(node);
            assert_eq!(returned_left, left);
        }
    }
}

#[cfg(test)]
mod multi_pass {
    use crate::{HeapPasses, HeapRank, HeapType};
    use super::LinkedRankPairingHeap;

    /*
      [5,3,4,1,8,9,6,7,2]

      1 = 0
      1 -> 3 = 1
      5 = 0
      4 -> 5 = 1
      1 -> 4 -> (5, 3) = 2
      8 = 0
      8 -> 9 = 1
      6 = 0
      6 -> 7 = 1
      6 -> 8 -> (9, 7) = 2
      1 -> 6 -> (8, 4) -> ((9, 7), (5, 3)) = 3
      2 = 0
       -------
       roots: 1 -> 2
    */

    #[test]
    fn heapify_a_list() {
        let nums = vec![5,3,4,1,8,9,6,7,2];
        let heap = LinkedRankPairingHeap {
            heap_rank: HeapRank::One,
            heap_type: HeapType::Min,
            passes: HeapPasses::Multi,
            root: None,
            keys: Default::default(),
            len: nums.len(),
            _phantom_priority: Default::default(),
            _phantom_key: Default::default()
        };
        let list = nums
            .into_iter()
            .fold(None, | list, num | heap.add_node_to_roots(LinkedRankPairingHeap::create_node(num, num), list));
        unsafe {
            let root = heap.multi_pass(LinkedRankPairingHeap::concatenate_lists(list, (*(list.unwrap()).as_ptr()).parent, None));

            let first_root = root.unwrap();
            let second_root = (*first_root.as_ptr()).parent.unwrap();
            let first_child = (*first_root.as_ptr()).left.unwrap();
            let left_second_child = (*first_child.as_ptr()).left.unwrap();
            let next_second_child = (*first_child.as_ptr()).next.unwrap();
            let third_child_1_left = (*left_second_child.as_ptr()).left.unwrap();
            let third_child_2_next = (*left_second_child.as_ptr()).next.unwrap();
            let third_child_3_left = (*next_second_child.as_ptr()).left.unwrap();
            let third_child_4_next = (*next_second_child.as_ptr()).next.unwrap();

            assert_eq!((*first_root.as_ptr()).key, 1);
            assert_eq!((*first_root.as_ptr()).next, Some(second_root));
            assert_eq!((*first_root.as_ptr()).left, Some(first_child));

            assert_eq!((*second_root.as_ptr()).key, 2);
            assert_eq!((*second_root.as_ptr()).next, Some(first_root));
            assert_eq!((*second_root.as_ptr()).left, None);
            assert_eq!((*second_root.as_ptr()).parent, Some(first_root));

            assert_eq!((*first_child.as_ptr()).key, 6);
            assert_eq!((*first_child.as_ptr()).parent, Some(first_root));

            assert_eq!((*next_second_child.as_ptr()).parent, Some(first_child));
            assert_eq!((*next_second_child.as_ptr()).key, 4);

            assert_eq!((*left_second_child.as_ptr()).parent, Some(first_child));
            assert_eq!((*left_second_child.as_ptr()).key, 8);

            assert_eq!((*third_child_1_left.as_ptr()).parent, Some(left_second_child));
            assert_eq!((*third_child_1_left.as_ptr()).left, None);
            assert_eq!((*third_child_1_left.as_ptr()).next, None);
            assert_eq!((*third_child_1_left.as_ptr()).key, 9);

            assert_eq!((*third_child_2_next.as_ptr()).parent, Some(left_second_child));
            assert_eq!((*third_child_2_next.as_ptr()).left, None);
            assert_eq!((*third_child_2_next.as_ptr()).next, None);
            assert_eq!((*third_child_2_next.as_ptr()).key, 7);

            assert_eq!((*third_child_3_left.as_ptr()).parent, Some(next_second_child));
            assert_eq!((*third_child_3_left.as_ptr()).left, None);
            assert_eq!((*third_child_3_left.as_ptr()).next, None);
            assert_eq!((*third_child_3_left.as_ptr()).key, 5);

            assert_eq!((*third_child_4_next.as_ptr()).parent, Some(next_second_child));
            assert_eq!((*third_child_4_next.as_ptr()).left, None);
            assert_eq!((*third_child_4_next.as_ptr()).next, None);
            assert_eq!((*third_child_4_next.as_ptr()).key, 3);
        }
    }
}

#[cfg(test)]
mod single_pass {
    use crate::{HeapPasses, HeapRank, HeapType};
    use super::LinkedRankPairingHeap;

    /*
        key: 1, left: Some("3")
        key: 4, left: Some("5")
        key: 8, left: Some("9")
        key: 6, left: Some("7")
        key: 2, left: None
     */

    #[test]
    fn heapify_a_list() {
        let nums = vec![5,3,4,1,8,9,6,7,2];
        let heap = LinkedRankPairingHeap {
            heap_rank: HeapRank::One,
            heap_type: HeapType::Min,
            passes: HeapPasses::Single,
            root: None,
            keys: Default::default(),
            len: nums.len(),
            _phantom_priority: Default::default(),
            _phantom_key: Default::default()
        };
        let list = nums
            .into_iter()
            .fold(None, | list, num | heap.add_node_to_roots(LinkedRankPairingHeap::create_node(num, num), list));
        unsafe {
            let root = heap.single_pass(LinkedRankPairingHeap::concatenate_lists(list, (*(list.unwrap()).as_ptr()).parent, None));

            let first_root = root.unwrap();
            let left_of_first = (*first_root.as_ptr()).left.unwrap();
            let second_root = (*first_root.as_ptr()).next.unwrap();
            let left_of_second = (*second_root.as_ptr()).left.unwrap();
            let third_root = (*second_root.as_ptr()).next.unwrap();
            let left_of_third = (*third_root.as_ptr()).left.unwrap();
            let fourth_root = (*third_root.as_ptr()).next.unwrap();
            let left_of_fourth = (*fourth_root.as_ptr()).left.unwrap();
            let fifth_root = (*fourth_root.as_ptr()).next.unwrap();

            assert_eq!((*first_root.as_ptr()).key, 1);

            assert_eq!((*left_of_first.as_ptr()).key, 3);
            assert_eq!((*left_of_first.as_ptr()).parent, root);
            assert_eq!((*left_of_first.as_ptr()).left, None);
            assert_eq!((*left_of_first.as_ptr()).next, None);

            assert_eq!((*second_root.as_ptr()).key, 4);
            assert_eq!((*second_root.as_ptr()).parent, root);

            assert_eq!((*left_of_second.as_ptr()).key, 5);
            assert_eq!((*left_of_second.as_ptr()).parent, Some(second_root));
            assert_eq!((*left_of_second.as_ptr()).left, None);
            assert_eq!((*left_of_second.as_ptr()).next, None);

            assert_eq!((*third_root.as_ptr()).key, 8);
            assert_eq!((*third_root.as_ptr()).parent, Some(second_root));

            assert_eq!((*left_of_third.as_ptr()).key, 9);
            assert_eq!((*left_of_third.as_ptr()).parent, Some(third_root));
            assert_eq!((*left_of_third.as_ptr()).left, None);
            assert_eq!((*left_of_third.as_ptr()).next, None);

            assert_eq!((*fourth_root.as_ptr()).key, 6);
            assert_eq!((*fourth_root.as_ptr()).parent, Some(third_root));

            assert_eq!((*left_of_fourth.as_ptr()).key, 7);
            assert_eq!((*left_of_fourth.as_ptr()).parent, Some(fourth_root));
            assert_eq!((*left_of_fourth.as_ptr()).left, None);
            assert_eq!((*left_of_fourth.as_ptr()).next, None);

            assert_eq!((*fifth_root.as_ptr()).key, 2);
            assert_eq!((*fifth_root.as_ptr()).parent, Some(fourth_root));
            assert_eq!((*fifth_root.as_ptr()).next, root);
            assert_eq!((*fifth_root.as_ptr()).left, None);
        }
    }
}
