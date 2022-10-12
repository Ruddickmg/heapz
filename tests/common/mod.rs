extern crate heapz;

use rand;
use rand::Rng;
use heapz::{Heap, DecreaseKey};

#[derive(Hash, Copy, Clone, Eq, PartialEq, Debug)]
pub enum Element {
    Target,
    Node,
}

fn generate_numbers() -> Vec<i32> {
    let size = 1000;
    let mut rng = rand::thread_rng();
    (0..size).map(|_| rng.gen::<i32>()).collect()
}

pub mod pop {
    use std::cmp::{max, min};
    use super::{Heap, generate_numbers, Element};

    pub fn returns_the_first_value_from_min_heap<T: Heap<i32, i32>>(mut heap: T) {
        let numbers = generate_numbers();
        let mut smallest = numbers[0];
        numbers.into_iter().for_each(|n| {
            smallest = min(smallest, n);
            let _ = &mut heap.push(n, n);
        });
        assert_eq!(heap.pop(), Some(smallest));
    }

    pub fn returns_the_first_value_from_max_heap<T: Heap<i32, i32>>(mut heap: T) {
        let numbers = generate_numbers();
        let mut largest = numbers[0];
        numbers.into_iter().for_each(|n| {
            largest = max(largest, n);
            let _ = &mut heap.push(n, n);
        });
        assert_eq!(heap.pop(), Some(largest));
    }

    pub fn removes_the_first_value_from_min_heap<T: Heap<i32, i32>>(mut heap: T) {
        let numbers = generate_numbers();
        let mut cloned = numbers.clone();
        numbers.into_iter().for_each(|n| {
            let _ = &mut heap.push(n, n);
        });
        cloned.sort_by(|a, b| b.cmp(a));
        let _ = cloned.pop();
        let _ = heap.pop();
        assert_eq!(heap.top(), cloned.get(cloned.len() - 1));
    }

    pub fn removes_the_first_value_from_max_heap<T: Heap<i32, i32>>(mut heap: T) {
        let numbers = generate_numbers();
        let mut cloned = numbers.clone();
        let mut largest = numbers[0];
        let mut second_largest = largest;
        cloned.sort_by(|a, b| a.cmp(b));
        numbers.into_iter().for_each(|n| {
            second_largest = largest;
            largest = max(largest, n);
            let _ = &mut heap.push(n, n);
        });
        let _ = cloned.pop();
        let _ = heap.pop();
        assert_eq!(heap.top(), cloned.get(cloned.len() - 1));
    }

    pub fn returns_none_if_the_heap_is_empty<T: Heap<Element, i32>>(mut heap: T) {
        assert_eq!(heap.pop(), None);
    }

    pub fn returns_all_elements_from_smallest_to_largest_in_a_min_heap<T: Heap<i32, i32>>(mut heap: T) {
        let numbers = generate_numbers();
        let mut cloned = numbers.clone();
        numbers.into_iter().for_each(|n| {
            let _ = &mut heap.push(n, n);
        });
        cloned.sort_by(|a, b| b.cmp(a));
        while !cloned.is_empty() {
            assert_eq!(heap.pop(), cloned.pop());
        }
        assert_eq!(heap.pop(), None);
    }

    pub fn returns_all_elements_from_largest_to_smallest_in_a_max_heap<T: Heap<i32, i32>>(mut heap: T) {
        let numbers = generate_numbers();
        let mut cloned = numbers.clone();
        numbers.into_iter().for_each(|n| {
            let _ = &mut heap.push(n, n);
        });
        cloned.sort_by(|a, b| a.cmp(b));
        while !cloned.is_empty() {
            assert_eq!(heap.pop(), cloned.pop());
        }
        assert_eq!(heap.pop(), None);
    }
}

pub mod push {
    use super::{Element, Heap};

    pub fn adds_a_value_to_the_heap<T: Heap<Element, i32>>(mut heap: T) {
        let value = 1;
        let key = Element::Target;
        heap.push(key, value);
        assert_eq!(heap.top(), Some(&key));
    }

    pub fn adds_a_higher_item_to_the_heap_behind_a_lower_in_a_min_heap<T: Heap<Element, i32>>(mut heap: T) {
        let lower = 1;
        let higher = 2;
        heap.push(Element::Target, lower);
        heap.push(Element::Node, higher);
        assert_eq!(heap.top(), Some(&Element::Target));
    }

    pub fn adds_a_higher_item_to_the_heap_before_a_lower_in_a_max_heap<T: Heap<Element, i32>>(mut heap: T) {
        let lower = 1;
        let higher = 2;
        heap.push(Element::Node, lower);
        heap.push(Element::Target, higher);
        assert_eq!(heap.top(), Some(&Element::Target));
    }

    pub fn adds_a_lower_item_to_the_heap_before_a_higher_in_a_min_heap<T: Heap<Element, i32>>(mut heap: T) {
        let lower = 1;
        let higher = 2;
        heap.push(Element::Node, higher);
        heap.push(Element::Target, lower);
        assert_eq!(heap.top(), Some(&Element::Target));
    }

    pub fn adds_a_lower_item_to_the_heap_behind_a_higher_in_a_max_heap<T: Heap<Element, i32>>(mut heap: T) {
        let lower = 1;
        let higher = 2;
        heap.push(Element::Target, higher);
        heap.push(Element::Node, lower);
        assert_eq!(heap.top(), Some(&Element::Target));
    }
}

#[cfg(test)]
pub mod top {
    use std::cmp::{max, min};
    use super::{Heap, generate_numbers, Element};

    pub fn returns_the_first_value_in_min_a_heap<T: Heap<Element, i32>>(mut heap: T) {
        let mut numbers = generate_numbers();
        numbers.sort();
        numbers.reverse();
        let mut smallest = numbers.pop().unwrap();
        heap.push(Element::Target, smallest);
        numbers.into_iter().for_each(|n| {
            let _ = &mut heap.push(Element::Node, n);
        });
        assert_eq!(heap.top(), Some(&Element::Target));
    }

    pub fn returns_the_first_value_in_max_a_heap<T: Heap<Element, i32>>(mut heap: T) {
        let mut numbers = generate_numbers();
        numbers.sort();
        let largest = numbers.pop().unwrap();
        heap.push(Element::Target, largest);
        numbers.into_iter().for_each(|n| {
            let _ = &mut heap.push(Element::Node, n);
        });
        assert_eq!(heap.top(), Some(&Element::Target));
    }

    pub fn returns_none_if_the_heap_is_empty<T: Heap<Element, i32>>(heap: T) {
        assert_eq!(heap.top(), None);
    }
}

pub mod size {
    use super::{Heap, generate_numbers, Element};

    pub fn returns_the_correct_size_of_a_heap_after_adding_elements<T: Heap<i32, i32>>(mut heap: T) {
        let numbers = generate_numbers();
        let len = numbers.len();
        numbers.into_iter().for_each(|n| {
            let _ = &mut heap.push(n, n);
        });
        assert_eq!(heap.size(), len);
    }

    pub fn returns_the_correct_size_of_a_heap_after_removing_an_element<T: Heap<i32, i32>>(mut heap: T) {
        let numbers = generate_numbers();
        let len = numbers.len();
        numbers.into_iter().for_each(|n| {
            let _ = &mut heap.push(n, n);
        });
        let _ = heap.pop();
        let _ = heap.pop();
        assert_eq!(heap.size(), len - 2);
    }
}

pub mod update {
    use std::cmp::{min, max};
    use super::{DecreaseKey, generate_numbers, Element};

    pub fn will_update_a_specific_element_by_key_in_a_min_heap<T: DecreaseKey<Element, i32>>(mut heap: T) {
        let mut numbers = generate_numbers();
        let target = numbers.pop().unwrap();
        let mut cloned = numbers.clone();
        let mut smallest = target;
        numbers.into_iter().for_each(|n| {
            smallest = min(smallest, n);
            let _ = &mut heap.push(Element::Node, n);
        });
        heap.push(Element::Target, target);
        let next_smallest = smallest - 1;
        cloned.sort_by(| a, b| b.cmp(a));
        heap.update(&Element::Target, next_smallest);
        assert_eq!(heap.pop(), Some(Element::Target));
    }

    pub fn will_update_a_specific_element_by_key_in_a_min_heap_after_pop<T: DecreaseKey<Element, i32>>(mut heap: T) {
        let mut numbers = generate_numbers();
        let mut cloned = numbers.clone();
        cloned.sort_by(|a, b| b.cmp(a));
        let target = cloned.remove(0);
        let index = numbers.iter().position(| n | n == &target).unwrap();
        numbers.remove(index);
        let mut smallest = target;
        numbers.into_iter().for_each(|n| {
            smallest = min(smallest, n);
            let _ = &mut heap.push(Element::Node, n);
        });
        heap.push(Element::Target, target);
        let prev_smallest = smallest + 1;
        heap.update(&Element::Target, prev_smallest);
        assert_eq!(heap.pop(), Some(Element::Node));
        assert_eq!(heap.pop(), Some(Element::Target));
    }

    pub fn will_update_a_specific_element_by_key_in_a_max_heap<T: DecreaseKey<Element, i32>>(mut heap: T) {
        let mut numbers = generate_numbers();
        let target = numbers.pop().unwrap();
        let mut cloned = numbers.clone();
        let mut largest = target;
        numbers.into_iter().for_each(|n| {
            largest = max(largest, n);
            let _ = &mut heap.push(Element::Node, n);
        });
        heap.push(Element::Target, target);
        let next_largest = largest + 1;
        cloned.sort_by(| a, b| a.cmp(b));
        heap.update(&Element::Target, next_largest);
        assert_eq!(heap.pop(), Some(Element::Target));
    }

    pub fn will_update_a_specific_element_by_key_in_a_max_heap_after_pop<T: DecreaseKey<Element, i32>>(mut heap: T) {
        let mut numbers = generate_numbers();
        let mut cloned = numbers.clone();
        cloned.sort_by(|a, b| a.cmp(b));
        let target = cloned.remove(0);
        let index = numbers.iter().position(| n | n == &target).unwrap();
        numbers.remove(index);
        let mut largest = target;
        numbers.into_iter().for_each(|n| {
            largest = max(largest, n);
            let _ = &mut heap.push(Element::Node, n);
        });
        heap.push(Element::Target, target);
        let prev_largest = largest - 1;
        heap.update(&Element::Target, prev_largest);
        assert_eq!(heap.pop(), Some(Element::Node));
        assert_eq!(heap.pop(), Some(Element::Target));
    }
}

pub mod delete {
    use std::cmp::{min, max};
    use super::{DecreaseKey, generate_numbers};

    pub fn will_delete_a_specific_element_by_key_from_min_heap<T: DecreaseKey<i32, i32>>(mut heap: T) {
        let mut numbers = generate_numbers();
        let mut cloned = numbers.clone();
        cloned.sort_by(|a, b| b.cmp(a));
        let target = cloned.remove(0);
        let index = numbers.iter().position(| n | n == &target).unwrap();
        numbers.remove(index);
        let mut largest = target;
        numbers.into_iter().for_each(|n| {
            largest = max(largest, n);
            let _ = &mut heap.push(n, n);
        });
        heap.push(target, target);
        heap.delete(&target);
        while !cloned.is_empty() {
            assert_eq!(heap.pop(), cloned.pop())
        }
    }

    pub fn will_delete_a_specific_element_by_key_from_min_heap_after_pop<T: DecreaseKey<i32, i32>>(mut heap: T) {
        let mut numbers = generate_numbers();
        let mut cloned = numbers.clone();
        cloned.sort_by(|a, b| b.cmp(a));
        let target = cloned.remove(0);
        let index = numbers.iter().position(| n | n == &target).unwrap();
        numbers.remove(index);
        let mut largest = target;
        numbers.into_iter().for_each(|n| {
            largest = max(largest, n);
            let _ = &mut heap.push(n, n);
        });
        let target = cloned.remove(0);
        heap.push(target, target);
        assert_eq!(heap.pop(), cloned.pop());
        heap.delete(&target);
        while !cloned.is_empty() {
            assert_eq!(heap.pop(), cloned.pop())
        }
    }

    pub fn will_delete_a_specific_element_by_key_from_max_heap<T: DecreaseKey<i32, i32>>(mut heap: T) {
        let mut numbers = generate_numbers();
        let mut cloned = numbers.clone();
        cloned.sort_by(|a, b| a.cmp(b));
        let target = cloned.remove(0);
        let index = numbers.iter().position(| n | n == &target).unwrap();
        numbers.remove(index);
        let mut smallest = target;
        numbers.into_iter().for_each(|n| {
            smallest = min(smallest, n);
            let _ = &mut heap.push(n, n);
        });
        heap.push(target, target);
        heap.delete(&target);
        while !cloned.is_empty() {
            assert_eq!(heap.pop(), cloned.pop())
        }
    }

    pub fn will_delete_a_specific_element_by_key_from_max_heap_after_pop<T: DecreaseKey<i32, i32>>(mut heap: T) {
        let mut numbers = generate_numbers();
        let mut cloned = numbers.clone();
        cloned.sort_by(|a, b| a.cmp(b));
        let target = cloned.remove(0);
        let index = numbers.iter().position(| n | n == &target).unwrap();
        numbers.remove(index);
        let mut smallest = target;
        numbers.into_iter().for_each(|n| {
            smallest = min(smallest, n);
            let _ = &mut heap.push(n, n);
        });
        let target = cloned.remove(0);
        heap.push(target, target);
        assert_eq!(heap.pop(), cloned.pop());
        heap.delete(&target);
        while !cloned.is_empty() {
            assert_eq!(heap.pop(), cloned.pop())
        }
    }
}