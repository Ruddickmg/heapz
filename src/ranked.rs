use crate::{DecreaseKey, Heap};
use std::{
    cmp::{max, Eq},
    collections::HashMap,
    hash::Hash,
};

#[derive(PartialEq)]
enum HeapType {
    Max,
    Min,
}

#[derive(PartialEq)]
enum HeapRank {
    One,
    Two,
}

#[derive(PartialEq)]
enum HeapPasses {
    Single,
    Multi,
}

type Position = Option<usize>;

struct Node<K: Hash + Eq + Copy, V: PartialOrd + PartialEq> {
    key: K,
    value: V,
    left: Position,
    next: Position,
    parent: Position,
    rank: usize,
    root: bool,
}

impl<K: Hash + Eq + Copy, V: PartialOrd + PartialEq> Node<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Node {
            key,
            value,
            left: None,
            next: None,
            parent: None,
            rank: 0,
            root: true,
        }
    }
    pub fn rank(&self) -> usize {
        self.rank.clone()
    }
    pub fn set_rank(&mut self, rank: usize) {
        self.rank = rank;
    }
    pub fn set_root(&mut self, root: bool) {
        self.root = root;
    }
}

pub struct RankedPairingHeap<K: Hash + Eq + Copy, V: PartialOrd + PartialEq> {
    root: Position,
    root_count: usize,
    heap_rank: HeapRank,
    heap_type: HeapType,
    passes: HeapPasses,
    list: Vec<Node<K, V>>,
    keys: HashMap<K, Position>,
}

// struct initialization
impl<K: Hash + Eq + Copy, V: PartialOrd + PartialEq> RankedPairingHeap<K, V> {
    fn new(heap_type: HeapType, heap_rank: HeapRank, passes: HeapPasses) -> Self {
        RankedPairingHeap {
            root: None,
            root_count: 0,
            heap_rank,
            heap_type,
            passes,
            list: vec![],
            keys: HashMap::new(),
        }
    }
    pub fn single_pass_max() -> Self {
        Self::new(HeapType::Max, HeapRank::One, HeapPasses::Single)
    }
    pub fn single_pass_max2() -> Self {
        Self::new(HeapType::Max, HeapRank::Two, HeapPasses::Single)
    }
    pub fn single_pass_min() -> Self {
        Self::new(HeapType::Min, HeapRank::One, HeapPasses::Single)
    }
    pub fn single_pass_min2() -> Self {
        Self::new(HeapType::Min, HeapRank::Two, HeapPasses::Single)
    }
    pub fn multi_pass_max() -> Self {
        Self::new(HeapType::Max, HeapRank::One, HeapPasses::Multi)
    }
    pub fn multi_pass_max2() -> Self {
        Self::new(HeapType::Max, HeapRank::Two, HeapPasses::Multi)
    }
    pub fn multi_pass_min() -> Self {
        Self::new(HeapType::Min, HeapRank::One, HeapPasses::Multi)
    }
    pub fn multi_pass_min2() -> Self {
        Self::new(HeapType::Min, HeapRank::Two, HeapPasses::Multi)
    }
}

// Ranking
impl<K, V> RankedPairingHeap<K, V>
where
    K: Hash + Eq + Copy,
    V: PartialOrd + PartialEq,
{
    fn rank1(left: i32, next: i32) -> i32 {
        if left != next {
            max(left, next)
        } else {
            left + 1
        }
    }

    fn rank2(left: i32, next: i32) -> i32 {
        max(left, next)
            + (if (&left as &i32 - &next as &i32).abs() > 1 {
                0
            } else {
                1
            })
    }

    fn rank(&self, left: i32, next: i32) -> usize {
        (match self.heap_rank {
            HeapRank::One => Self::rank1(left, next),
            HeapRank::Two => Self::rank2(left, next),
        }) as usize
    }

    fn rank_nodes(&self, left: Position, next: Position) -> usize {
        let left_rank = self.get_rank(left);
        let right_rank = self.get_rank(next);
        self.rank(left_rank, right_rank)
    }

    fn get_rank(&self, position: Position) -> i32 {
        if let Some(n) = self.get_node(position) {
            n.rank as i32
        } else {
            0 - 1
        }
    }

    fn update_rank(&mut self, position: Position) {
        self.get_links(position).map(|(_, left, next)| {
            let rank = self.rank_nodes(left, next);
            self.get_node_mut(position).map(|mut node| {
                node.rank = rank;
            });
        });
    }

    fn update_ranks(&mut self, mut position: Position) {
        while position.is_some() && !self.is_root(position) {
            self.update_rank(position);
            position = self.get_parent_index(position);
        }
    }
}

// storage interaction
impl<K, V> RankedPairingHeap<K, V>
where
    K: Hash + Eq + Copy,
    V: PartialOrd + PartialEq,
{
    fn get_node(&self, position: Position) -> Option<&Node<K, V>> {
        position.map(|index| self.list.get(index)).unwrap_or(None)
    }

    fn get_node_mut(&mut self, position: Position) -> Option<&mut Node<K, V>> {
        if let Some(index) = position {
            self.list.get_mut(index)
        } else {
            None
        }
    }

    fn remove_array_node(&mut self, position: Position) -> Option<Node<K, V>> {
        self.get_node(self.last_position())
            .map(|node| node.key)
            .map(|key| {
                self.keys.remove(&key);
                self.keys.insert(key, position);
            });
        position.map(|index| self.list.swap_remove(index))
    }

    fn add_node(&mut self, node: Node<K, V>) -> Position {
        let position = Some(self.list.len());
        self.keys.insert(node.key, position);
        self.list.push(node);
        position
    }

    fn get_position(&self, key: &K) -> Position {
        self.keys.get(key).cloned().unwrap_or(None)
    }
}

// utility functions
impl<K: Hash + Eq + Copy, V: PartialOrd + PartialEq> RankedPairingHeap<K, V> {
    fn last_position(&self) -> Position {
        let size = self.size();
        if size > 0 {
            Some(size - 1)
        } else {
            None
        }
    }

    fn is_left(&self, position: Position, parent: Position) -> bool {
        self.get_node(parent)
            .map(|parent| parent.left == position)
            .unwrap_or(false)
    }

    fn is_root(&self, position: Position) -> bool {
        self.get_node(position)
            .map(|node| node.root)
            .unwrap_or(false)
    }

    fn get_value(&self, position: Position) -> Option<&V> {
        self.get_node(position).map(|node| &node.value)
    }

    fn get_key(&self, position: Position) -> Option<&K> {
        self.get_node(position).map(|node| &node.key)
    }

    fn get_index<F: Fn(&Node<K, V>) -> Position>(
        &self,
        index: Position,
        get_adjacent: F,
    ) -> Position {
        self.get_node(index).map(get_adjacent).unwrap_or(None)
    }

    fn get_left_index(&self, index: Position) -> Position {
        self.get_index(index, |node| node.left)
    }

    fn get_next_index(&self, index: Position) -> Position {
        self.get_index(index, |node| node.next)
    }

    fn get_parent_index(&self, index: Position) -> Position {
        self.get_index(index, |node| node.parent)
    }

    fn get_links(&self, position: Position) -> Option<(Position, Position, Position)> {
        self.get_node(position)
            .map(|node| (node.parent, node.left, node.next))
    }

    fn get_siblings(&self, position: Position) -> Option<(Position, Position)> {
        self.get_links(position)
            .map(|(parent, _, next)| (parent, next))
    }

    fn link_next(&mut self, parent: Position, next: Position) {
        self.get_node_mut(parent).map(|node| {
            node.next = next;
        });
        self.get_node_mut(next).map(|node| {
            node.parent = parent;
        });
    }

    fn link_left(&mut self, parent: Position, left: Position) {
        self.get_node_mut(parent).map(|node| {
            node.left = left;
        });
        self.get_node_mut(left).map(|node| {
            node.parent = parent;
        });
    }

    fn unlink_parent(&mut self, child: Position) {
        let parent = self.get_parent_index(child);
        self.get_node_mut(parent).map(|node| {
            if node.next == child {
                node.next = None;
            }
            if node.left == child {
                node.left = None;
            }
        });
        self.get_node_mut(child).map(|node| {
            node.parent = None;
        });
    }

    fn compare_values<T: PartialOrd>(&self, value_a: T, value_b: T) -> bool {
        if self.heap_type == HeapType::Max {
            value_a > value_b
        } else {
            value_a < value_b
        }
    }

    fn compare(&self, a: Position, b: Position) -> bool {
        self.get_value(a)
            .zip(self.get_value(b))
            .map_or(false, |(value_a, value_b)| {
                self.compare_values(value_a, value_b)
            })
    }

    fn merge_trees(&mut self, parent: Position, child: Position) -> Position {
        let left = self.get_left_index(parent);
        let rank = (self.get_rank(child) + 1) as usize;
        self.link_next(child, left);
        self.link_left(parent, child);
        self.get_node_mut(parent).map(|node| node.set_rank(rank));
        self.get_node_mut(child).map(|node| node.set_root(false));
        parent
    }

    fn link(&mut self, node_a: Position, node_b: Position) -> Position {
        if node_b != node_a {
            match (node_a, node_b) {
                (Some(_), Some(_)) => if self.compare(node_a, node_b) {
                    self.merge_trees(node_a, node_b)
                } else {
                    self.merge_trees(node_b, node_a)
                },
                (Some(_), None) => node_a,
                (None, Some(_)) => node_b,
                _ => None,
            }
        } else {
            node_a.or(node_b)
        }
    }

    fn unlink(&mut self, position: Position) -> Position {
        self.get_siblings(position)
            .map(|(parent, next)| self.link_next(parent, next));
        self.get_node_mut(position).map(|node| {
            node.parent = None;
            node.next = None;
        });
        position
    }

    fn update_root(&mut self, replacement: Position) {
        self.root = if self.size() <= 0 { None } else { replacement }
    }

    fn swap_remove_with_tree(&mut self, position: Position) -> Option<Node<K, V>> {
        let last = self.last_position();
        let is_last_node = self.is_linked_to_self(position);
        self.get_links(last)
            .map(|(parent_of_last, left_of_last, next_of_last)| {
                self.remove_array_node(position).map(|removed| {
                    if !is_last_node {
                        self.link_next(removed.parent, removed.next);
                        self.link_left(position, left_of_last);
                        if last != position {
                            self.link_next(
                                if parent_of_last == position {
                                    if next_of_last == position {
                                        position
                                    } else {
                                        removed.parent
                                    }
                                } else {
                                    parent_of_last
                                },
                                position,
                            );
                            self.link_next(
                                position,
                                if next_of_last == position {
                                    if parent_of_last == position {
                                        position
                                    } else {
                                        removed.next
                                    }
                                } else {
                                    next_of_last
                                },
                            );
                        }
                    }
                    removed
                })
            })
            .unwrap_or(None)
    }

    fn is_linked_to_self(&self, position: Position) -> bool {
        self.get_siblings(position)
            .map(|(parent, next)| next == position && parent == position)
            .unwrap_or(false)
    }

    fn get_next_root(&mut self, position: Position) -> Position {
        let last = self.last_position();
        let next = self.get_next_index(position);
        if self.is_linked_to_self(position) {
            None
        } else if next == last {
            position
        } else {
            next
        }
    }

    fn swap_remove_with_branch(&mut self, position: Position) -> Option<Node<K, V>> {
        let last = self.last_position();
        self.get_links(last)
            .map(|(parent, left, next)| {
                let is_left = self.is_left(last, parent);
                self.remove_array_node(position).map(|mut removed| {
                    self.link_next(removed.parent, removed.next);
                    self.link_next(position, next);
                    self.link_left(position, left);
                    let parent_of_last = if removed.left == last {
                        removed.left = position;
                        last
                    } else {
                        parent
                    };
                    if is_left {
                        self.link_left(parent_of_last, position);
                    } else {
                        self.link_next(parent_of_last, position);
                    }
                    removed
                })
            })
            .unwrap_or(None)
    }

    fn remove(&mut self, position: Position) -> Option<Node<K, V>> {
        if self.is_root(self.last_position()) {
            self.swap_remove_with_tree(position)
        } else {
            self.swap_remove_with_branch(position)
        }
    }

    fn single_pass(&mut self, mut node: Position) -> Position {
        let mut bucket: HashMap<i32, Position> = HashMap::new();
        let mut root = None;
        while node.is_some() {
            let rank = self.get_rank(node);
            let next = self.get_next_index(node);
            node = self.unlink(node);
            if let Some(matched) = bucket.remove(&rank) {
                let linked = self.link(node, matched);
                root = self.add_root_to_list(linked, root);
            } else {
                bucket.insert(rank, node);
            }
            node = next;
        }
        bucket
            .drain()
            .fold(root, |list, (_, node)| self.add_root_to_list(node, list))
    }

    fn multi_pass(&mut self, mut node: Position) -> Position {
        let mut bucket: HashMap<i32, Position> = HashMap::new();
        let mut root = None;
        while node.is_some() {
            let rank = self.get_rank(node);
            let next = self.get_next_index(node);
            self.unlink(node);
            if let Some(matched) = bucket.remove(&rank) {
                if matched == root {
                    root = if self.is_linked_to_self(root) {
                        None
                    } else {
                        self.get_next_index(matched)
                    }
                }
                let unlinked = self.unlink(matched);
                node = self.link(node, unlinked);
            }
            if bucket.contains_key(&self.get_rank(node)) {
                self.link_next(node, next);
            } else {
                bucket.insert(rank, node);
                root = self.add_root_to_list(node, root);
                node = next;
            }
        }
        root
    }

    fn combine_ranks(&mut self, node: Position) -> Position {
        if self.passes == HeapPasses::Single {
            self.single_pass(node)
        } else {
            self.multi_pass(node)
        }
    }

    fn add_root_to_list(&mut self, root: Position, list: Position) -> Position {
        self.get_node_mut(root).map(|node| node.set_root(true));
        if list.is_some() {
            if let Some((parent, next)) = self.get_siblings(list) {
                let is_new_root = self.compare(root, list);
                self.link_next(if is_new_root { parent } else { list }, root);
                self.link_next(root, if is_new_root { list } else { next });
                if is_new_root {
                    root
                } else {
                    list
                }
            } else {
                list
            }
        } else {
            self.link_next(root, root);
            root
        }
    }

    fn concatenate_lists(&mut self, head_list: Position, tail_list: Position) -> Position {
        let tail = self.get_parent_index(head_list);
        self.unlink_parent(head_list);
        self.unlink_parent(tail_list);
        self.link_next(tail, tail_list);
        head_list.or(tail_list)
    }

    fn unlink_node_from_tree(&mut self, position: Position, mut root: Position) -> Position {
        if self.is_root(position) {
            if position != root {
                self.unlink(position);
            }
        } else if let Some((parent, _, next)) = self.get_links(position) {
            if self.is_left(position, parent) {
                self.link_left(parent, next);
            } else {
                self.link_next(parent, next);
            }
        }
        position
    }
}

impl<K, V> Heap<K, V> for RankedPairingHeap<K, V>
where
    K: Hash + Eq + Copy,
    V: PartialOrd,
{
    fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    fn size(&self) -> usize {
        self.list.len()
    }

    fn push(&mut self, key: K, value: V) {
        let node = Node::new(key, value);
        let position = self.add_node(node);
        let root = self.add_root_to_list(position, self.root);
        self.update_root(root);
    }

    fn top(&self) -> Option<&K> {
        self.get_key(self.root)
    }

    fn top_mut(&mut self) -> Option<&mut K> {
        self.get_node_mut(self.root).map(|node| &mut node.key)
    }

    fn pop(&mut self) -> Option<K> {
        let root = self.root;
        if root.is_some() {
            let next_root = self.get_next_root(root);
            self.remove(root).map(|removed| {
                let head = self.concatenate_lists(next_root, removed.left);
                let root = self.combine_ranks(head);
                self.update_root(root);
                removed.key
            })
        } else {
            None
        }
    }
}

impl<K, V> DecreaseKey<K, V> for RankedPairingHeap<K, V>
where
    K: Hash + Eq + Copy,
    V: PartialOrd,
{
    fn update(&mut self, key: &K, value: V) {
        let position = self.get_position(key);
        self.get_value(position)
            .map(|current| self.compare_values(&value, current))
            .map(|can_update| {
                if can_update {
                    self.unlink_node_from_tree(position, self.root);
                    self.get_node_mut(position).map(|node| {
                        node.value = value;
                    });
                    self.root = self.add_root_to_list(position, self.root);
                }
            });
    }

    fn delete(&mut self, key: &K) -> Option<K> {
        let position = self.get_position(key);
        let root = self.root;
        self.root = self.unlink_node_from_tree(position, self.root);
        let deleted = self.pop();
        self.root = root;
        deleted
    }
}