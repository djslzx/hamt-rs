#![feature(asm)]
#![allow(dead_code)]

mod util;
mod linked_list;
mod deque;

use crate::util::{
    bitrank,
    bitarr::{
        b64, b128,
    },
};
use std::{
    fmt,
    hash::{Hash},
    collections::{
        HashMap,
    }
};
use fasthash::murmur3::hash128_with_seed;

// Constants
const N_CHILDREN: usize = 64;
const LOG_N_CHILDREN: usize = 6;

// Structs
#[derive(PartialEq)]
pub struct Node<K,V>
    where K: Hash
{
    occupied: u64,
    children: Vec<Child<K,V>>,
}

pub type Tree<K,V> = Option<Box<Node<K,V>>>;

#[derive(Debug, PartialEq)]
pub struct Hamt<K,V>
    where K: Hash
{
    root: Tree<K,V>,
    seed: u32,
}

#[derive(Debug, PartialEq)]
enum Child<K,V>
    where K: Hash
{
    KVPair(K, V),
    AMTNode(Tree<K,V>),
}

impl<K,V> Node<K,V>
    where K: Hash + AsRef<[u8]> + PartialEq
{
    fn new() -> Node<K,V> {
        Node {
            occupied: 0,
            children: Vec::new(),
        }
    }
    fn new_tree() -> Tree<K,V> {
        Some(Box::new(Self::new()))
    }
    fn occupied_at(&self, i: usize) -> bool {
        b64::get(self.occupied, i)
    }
    fn set_occupied(&mut self, i: usize) {
        self.occupied = b64::set(self.occupied, i);
    }
    fn set_unoccupied(&mut self, i: usize) {
        self.occupied = b64::unset(self.occupied, i);
    }
    fn insert_child(&mut self, i: usize, c: Child<K,V>) {
        self.children.insert(i, c);
    }
    fn replace_child(&mut self, i: usize, c: Child<K,V>) {
        self.children.remove(i);
        self.children.insert(i, c);
    }
    fn remove_child(&mut self, i: usize) -> Child<K,V> {
        self.children.remove(i)
    }
}

impl<K,V> fmt::Debug for Node<K,V>
    where K: Hash + fmt::Debug, V: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Tree")
            .field("occupied", &format_args!("0x{:x}", self.occupied))
            .field("children", &self.children)
            .finish()
    }
}

impl<K,V> Hamt<K,V>
    where K: Clone + Hash + AsRef<[u8]> + PartialEq + Copy + fmt::Debug,
          V: Clone + Copy + fmt::Debug
{
    fn new() -> Hamt<K,V> {
        Self::with_seed(0)
    }
    fn with_seed(seed: u32) -> Hamt<K,V> {
        Hamt {
            root: Node::new_tree(),
            seed,
        }
    }
    fn hash(key: K, seed: u32) -> u128 {
        hash128_with_seed(key, seed)
    }
    fn get_slot(hash: u128, level: usize) -> usize {
        assert!((level+1) * LOG_N_CHILDREN < 128, "level={}", level);
        b128::get_bits(hash,
                       level * LOG_N_CHILDREN,
                       (level+1) * LOG_N_CHILDREN) as usize
    }
    fn choose_child(node: &Node<K,V>, slot: usize) -> usize {
        (if slot == 0 {0} else {bitrank(node.occupied, slot-1)}) as usize
    }
    fn insert_into_node(node: &mut Node<K,V>, key: K, val: V, hash: u128, level: usize, seed: u32) {
        let slot = Self::get_slot(hash, level);
        let n = Self::choose_child(node, slot);
        if node.occupied_at(slot) {
            match node.children.get_mut(n).unwrap() {
                Child::KVPair(k, v) => {
                    if *k == key {
                        // if occupied by entry with the same key, update value
                        *v = val;
                    } else {
                        // if occupied by entry with different key, replace with subtree
                        let mut subtree = Node::new_tree();
                        let mut subnode = subtree.as_mut().unwrap();
                        let old_hash = Self::hash(*k, seed);
                        Self::insert_into_node(&mut subnode, *k, *v, old_hash, level+1, seed);
                        Self::insert_into_node(&mut subnode, key, val, hash, level+1, seed);
                        node.replace_child(n, Child::AMTNode(subtree));
                    }
                }
                Child::AMTNode(tree) => {
                    // if subtree, then enter subtree and recursively insert
                    Self::insert_into_node(tree.as_mut().unwrap(), key, val, hash, level+1, seed);
                }
            }
        } else {
            // add the k-v pair, set occupied
            node.set_occupied(slot);
            node.insert_child(n, Child::KVPair(key, val));
        }
    }
    fn lookup_in_node(node: &Node<K,V>, key: K, hash: u128, level: usize) -> Option<V> {
        let slot = Self::get_slot(hash, level);
        if node.occupied_at(slot) {
            let n = Self::choose_child(node, slot);
            match node.children.get(n).unwrap() {
                Child::KVPair(k, v) =>
                    if *k == key {
                        Some(*v)
                    } else {
                        None
                    },
                Child::AMTNode(tree) =>
                    Self::lookup_in_node(tree.as_ref().unwrap(), key, hash, level+1),
            }
        } else {
            None
        }
    }
    fn delete_in_node(parent: &mut Node<K,V>, key: K, hash: u128, level: usize, slot: usize, n: usize) -> Option<V> {
        if !parent.occupied_at(slot) {
            None
        } else {
            // If child is kvpair, then remove
            // If parent's child has 2 children, then:
            // (1) If grandchild to remove is a kvpair, then replace the child with the other grandchild
            // (2) If grandchild to remove is a tree, then "recurse"
            match parent.children.get_mut(n).unwrap() {
                Child::KVPair(k, v) => {
                    if *k == key {
                        let val = *v;
                        parent.remove_child(n);
                        parent.set_unoccupied(slot);
                        Some(val)
                    } else {
                        None
                    }
                }
                Child::AMTNode(child) => {
                    let child = child.as_mut().unwrap();
                    let child_slot = Self::get_slot(hash, level+1);
                    let child_n = Self::choose_child(child, child_slot);
                    if child.children.len() == 2 {
                        let other_child_n = !child_n;
                        match child.children.get(child_n).unwrap() {
                            Child::KVPair(_, v) => {
                                // pull up the other child if it's a KV pair
                                let val = *v;
                                let grandchild = child.remove_child(other_child_n);
                                parent.insert_child(child_n, grandchild);
                                Some(val)
                            }
                            Child::AMTNode(_) => {
                                Self::delete_in_node(child, key, hash, level+1, child_slot, child_n)
                            }
                        }
                    } else {
                        Self::delete_in_node(child, key, hash, level+1, child_slot, child_n)
                    }
                }
            }
        }
    }
    fn raw_insert(&mut self, hash: u128, key: K, val: V) {
        Self::insert_into_node(&mut self.root.as_mut().unwrap(), key, val, hash, 0, self.seed)
    }
    fn raw_get(&self, hash: u128, key: K) -> Option<V> {
        let root = self.root.as_ref().unwrap();
        Self::lookup_in_node(root, key, hash, 0)
    }
    fn raw_remove(&mut self, hash: u128, key: K) -> Option<V> {
        let slot = Self::get_slot(hash, 0);
        let n = Self::choose_child(&self.root.as_mut().unwrap(), slot);
        Self::delete_in_node(&mut self.root.as_mut().unwrap(), key, hash, 0, slot, n)
    }
    fn insert(&mut self, key: K, val: V) {
        let hash = Self::hash(key, self.seed);
        self.raw_insert(hash, key, val);
    }
    fn get(&self, key: K) -> Option<V> {
        let hash = Self::hash(key, self.seed);
        self.raw_get(hash, key)
    }
    fn remove(&mut self, key: K) -> Option<V> {
        let hash = Self::hash(key, self.seed);
        self.raw_remove(hash, key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type TestHamt<'a> = Hamt<&'a str, i32>;

    #[test]
    fn test_get_slot() {
        assert_eq!(TestHamt::get_slot(0b1000000, 0), 0);
        assert_eq!(TestHamt::get_slot(0b1000000, 1), 1);
        assert_eq!(TestHamt::get_slot(0b11000000, 1), 0b11);
        assert_eq!(TestHamt::get_slot(0b1000000111111000000, 1), 0b111111);
        assert_eq!(TestHamt::get_slot(0b1000000111111000000, 2), 0);
        assert_eq!(TestHamt::get_slot(0b1000000111111000000, 3), 1);
    }

    #[test]
    fn test_insert_root_level() {
        let mut hamt = Hamt::new();
        // First insert
        hamt.insert("peter", 2);
        let hash = TestHamt::hash("peter", hamt.seed);
        let slot = TestHamt::get_slot(hash, 0);
        // Check occupied bit
        for i in 0..N_CHILDREN {
            assert_eq!(b64::get(hamt.root.as_ref().unwrap().occupied, i), i == slot);
        }
        // Check children
        assert_eq!(hamt.root.as_ref().unwrap().children.len(), 1);
        assert_eq!(*hamt.root.as_ref().unwrap().children.first().unwrap(),
                   Child::KVPair("peter", 2));

        // Update value
        hamt.insert("peter", 5);
        // Check occupied bit
        for i in 0..N_CHILDREN {
            assert_eq!(b64::get(hamt.root.as_ref().unwrap().occupied, i), i == slot);
        }
        // Check children
        assert_eq!(hamt.root.as_ref().unwrap().children.len(), 1);
        assert_eq!(*hamt.root.as_ref().unwrap().children.first().unwrap(),
                   Child::KVPair("peter", 5));

        // Insert second kv pair
        hamt.insert("david", 5);
        let hash2 = TestHamt::hash("david", hamt.seed);
        let slot2 = TestHamt::get_slot(hash2, 0);
        // Check occupied bit
        for i in 0..N_CHILDREN {
            assert_eq!(b64::get(hamt.root.as_ref().unwrap().occupied, i),
                       i == slot || i == slot2,
                       "i={}, occupieds={:b}, slot1={}, slot2={}",
                       i, hamt.root.as_ref().unwrap().occupied, slot, slot2);
        }
        // Check children
        assert_eq!(hamt.root.as_ref().unwrap().children.len(), 2);
        assert!(hamt.root.as_ref().unwrap().children.contains(&Child::KVPair("peter", 5)));
        assert!(hamt.root.as_ref().unwrap().children.contains(&Child::KVPair("david", 5)));

        // Update peter again
        hamt.insert("peter", 3);
        // Check occupied bit
        for i in 0..N_CHILDREN {
            assert_eq!(b64::get(hamt.root.as_ref().unwrap().occupied, i), i == slot || i == slot2);
        }
        // Check children
        assert_eq!(hamt.root.as_ref().unwrap().children.len(), 2);
        assert!(hamt.root.as_ref().unwrap().children.contains(&Child::KVPair("peter", 3)));
        assert!(hamt.root.as_ref().unwrap().children.contains(&Child::KVPair("david", 5)));
    }

    #[test]
    fn test_get() {
        let mut hamt = Hamt::new();
        let mut dict = HashMap::new();
        let kvs = vec![
            ("a", 1), ("b", 2), ("c", 3), ("c", 4),
        ];
        for (k,v) in kvs.iter() {
            hamt.insert(k, v);
            dict.insert(*k, *v);
        }
        for (k, _) in kvs.iter() {
            assert_eq!(hamt.get(k), dict.get(*k));
        }
        // Check that we don't get false positives
        let keys = vec![
            "d", "e", "f",
        ];
        for k in keys.iter() {
            assert_eq!(hamt.get(k), None);
        }
    }

    #[test]
    fn test_remove() {
        let mut hamt = Hamt::new();
        let kvs = vec![
            ("a", 1), ("b", 2), ("c", 3), ("d", 4)
        ];
        for (k,v) in kvs.iter() {
            hamt.insert(k, v);
        }
        println!("{:?}", hamt);
        for (k, _) in kvs.iter() {
            hamt.remove(k);
            assert_eq!(hamt.get(k), None);
        }
    }

    #[test]
    fn test_insert_tree() {
        let mut hamt = Hamt::new();
        let items: Vec<(u128, &str, i32)> = vec![
            (0b0_000000_000000, "a", 1),
            (0b0_000001_000000, "b", 2),
            (0b1_000001_000000, "c", 3),
        ];
        for (h, k, v) in items.iter() {
            hamt.raw_insert(*h, *k, *v);
        }
        println!("{:?}", hamt);
        assert_eq!(
            hamt,
            TestHamt { root: Some(Box::new(Node {
                occupied: 0x1,
                children: vec![
                    Child::AMTNode(Some(Box::new(Node {
                        occupied: 0x400000002,
                        children: vec![
                            Child::AMTNode(Some(Box::new(Node {
                                occupied: 0x2000000000000002,
                                children: vec![
                                    Child::KVPair("c", 3),
                                    Child::KVPair("b", 2)
                                ]
                            }))),
                            Child::KVPair("a", 1)]
                    })))]
            })),
                seed: 0 });
    }
}

fn main() {

}