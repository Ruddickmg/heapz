use crate::Heap;
use std::hash::Hash;

type BoxedNode<K, V> = Box<Node<K, V>>;

struct Node<K, V: PartialOrd> {
    pub value: V,
    pub key: K,
    left: Option<BoxedNode<K, V>>,
    next: Option<BoxedNode<K, V>>,
}

impl<K, V: PartialOrd> Node<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Node {
            key,
            value,
            left: None,
            next: None,
        }
    }
    pub fn value(self) -> V {
        self.value
    }
    pub fn set_left(&mut self, node: Option<BoxedNode<K, V>>) {
        self.left = node;
    }
    pub fn set_next(&mut self, node: Option<BoxedNode<K, V>>) {
        self.next = node;
    }
    pub fn left(self) -> Option<BoxedNode<K, V>> {
        self.left
    }
    pub fn next(self) -> Option<BoxedNode<K, V>> {
        self.next
    }
}

pub struct PairingHeap<K, V: PartialOrd> {
    root: Option<BoxedNode<K, V>>,
    heap_type: HeapType,
    size: usize,
}

#[derive(PartialEq)]
enum HeapType {
    Max,
    Min,
}

impl<K, V: PartialOrd> PairingHeap<K, V> {
    pub fn min() -> Self {
        Self::new(HeapType::Min)
    }
    pub fn max() -> Self {
        Self::new(HeapType::Max)
    }

    fn new(heap_type: HeapType) -> Self {
        PairingHeap {
            root: None,
            heap_type,
            size: 0,
        }
    }

    fn compare(&self, a: &BoxedNode<K, V>, b: &BoxedNode<K, V>) -> bool {
        match self.heap_type {
            HeapType::Max => a.value >= b.value,
            HeapType::Min => a.value <= b.value,
        }
    }

    fn add_child(mut parent: BoxedNode<K, V>, mut child: BoxedNode<K, V>) -> BoxedNode<K, V> {
        if parent.left.is_some() {
            child.set_next(parent.left.take());
        }
        parent.set_left(Some(child));
        parent
    }

    fn merge(
        &mut self,
        node_a: Option<BoxedNode<K, V>>,
        node_b: Option<BoxedNode<K, V>>,
    ) -> Option<BoxedNode<K, V>> {
        match (node_a, node_b) {
            (Some(a), Some(b)) => Some(if self.compare(&a, &b) {
                Self::add_child(a, b)
            } else {
                Self::add_child(b, a)
            }),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            _ => None,
        }
    }

    fn two_pass_merge(&mut self, node: Option<BoxedNode<K, V>>) -> Option<BoxedNode<K, V>> {
        let mut root = node;
        let mut merged: Option<BoxedNode<K, V>> = None;

        while let Some(mut parent) = root {
            if let Some(mut child) = parent.next.take() {
                root = child.next.take();
                let children = self.merge(Some(parent), Some(child));
                merged = self.merge(merged, children);
            } else {
                merged = self.merge(merged, Some(parent));
                root = None;
            }
        }
        merged
    }
}

impl<K: Hash + Eq, V: PartialOrd> Heap<K, V> for PairingHeap<K, V> {
    fn is_empty(&self) -> bool {
        self.root.is_some()
    }

    fn size(&self) -> usize {
        self.size.clone()
    }

    fn push(&mut self, key: K, value: V) {
        self.root = if self.root.is_some() {
            let root = self.root.take();
            self.merge(root, Some(Box::new(Node::new(key, value))))
        } else {
            Some(Box::new(Node::new(key, value)))
        };
        self.size += 1;
    }

    fn top(&self) -> Option<&K> {
        self.root.as_ref().map(|node| &node.key)
    }

    fn top_mut(&mut self) -> Option<&mut K> {
        self.root.as_mut().map(|node| &mut node.key)
    }

    fn pop(&mut self) -> Option<K> {
        self.root.take().map(|mut node| {
            self.size -= 1;
            self.root = self.two_pass_merge(node.left.take());
            node.key
        })
    }
}