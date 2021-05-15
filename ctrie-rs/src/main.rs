#![feature(asm)]
#![allow(dead_code)]

mod util;
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
#[derive(Debug)]
pub struct Hamt<K,V>
    where K: Hash
{
    root: Tree<K,V>,
    seed: u32,
}

#[derive(PartialEq)]
pub struct Tree<K,V>
    where K: Hash
{
    occupied: u64,
    children: Vec<Child<K,V>>,
}

#[derive(Debug, PartialEq)]
enum Child<K,V>
    where K: Hash
{
    KVPair(K, V),
    AMTNode(Tree<K,V>),
}

impl<K,V> Tree<K,V>
    where K: Hash + AsRef<[u8]> + PartialEq
{
    fn new() -> Tree<K,V> {
        Tree {
            occupied: 0,
            children: Vec::new(),
        }
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

impl<K,V> fmt::Debug for Tree<K,V>
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
    where K: Clone + Hash + AsRef<[u8]> + PartialEq + Copy,
          V: Clone + Copy
{
    fn new() -> Hamt<K,V> {
        Self::with_seed(0)
    }
    fn with_seed(seed: u32) -> Hamt<K,V> {
        Hamt {
            root: Tree {
                occupied: 0,
                children: Vec::new(),
            },
            seed,
        }
    }
    fn hash(key: K, seed: u32) -> u128 {
        hash128_with_seed(key, seed)
    }
    fn get_slot(hash: u128, level: usize) -> usize {
        b128::get_bits(hash,
                       level * LOG_N_CHILDREN,
                       (level+1) * LOG_N_CHILDREN) as usize
    }
    fn choose_child(node: &Tree<K,V>, slot: usize) -> usize {
        (if slot == 0 {0} else {bitrank(node.occupied, slot-1)}) as usize
    }
    fn insert_into_node(node: &mut Tree<K,V>, key: K, val: V, hash: u128, level: usize) {
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
                        let mut subtree = Tree::new();
                        Self::insert_into_node(&mut subtree, *k, *v, hash, level+1);
                        Self::insert_into_node(&mut subtree, key, val, hash, level+1);
                        node.replace_child(n, Child::AMTNode(subtree));
                    }
                }
                Child::AMTNode(tree) => {
                    // if subtree, then enter subtree and recursively insert
                    Self::insert_into_node(tree, key, val, hash, level+1);
                }
            }
        } else {
            // add the k-v pair, set occupied
            node.set_occupied(slot);
            node.insert_child(n, Child::KVPair(key, val));
        }
    }
    fn lookup_in_node(node: &Tree<K,V>, key: K, hash: u128, level: usize) -> Option<V> {
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
                    Self::lookup_in_node(tree, key, hash, level+1),
            }
        } else {
            None
        }
    }
    fn delete_in_node(node: &mut Tree<K,V>, key: K, hash: u128, level: usize, slot: usize, n: usize) -> Option<V> {
        if node.occupied_at(slot) {
            match node.children.get_mut(n).unwrap() {
                Child::KVPair(_, v) => {
                    let val = *v;
                    node.remove_child(n);
                    Some(val)
                }
                Child::AMTNode(tree) => {
                    let sub_slot = Self::get_slot(hash, level+1);
                    let sub_n = Self::choose_child(&tree, sub_slot);
                    debug_assert!(tree.children.len() > 1);
                    if tree.children.len() == 2 {
                        // If subtree has 2 elts:
                        // - if the removed elt is a KV pair, then drop tree and pull the other child up
                        // - if the removed elt is a tree, then recurse on the tree
                        let other_n = !sub_n; // tree has 2 entries, so the other entry is indexed by sub_n's complement
                        let c = tree.children.get(other_n).unwrap();
                        match tree.children.get(sub_n).unwrap() {
                            Child::KVPair(_, v) => {
                                node.insert_child(n, *c);
                                Some(*v)
                            }
                            Child::AMTNode(_) => {
                                Self::delete_in_node(tree, key, hash, level+1, sub_slot, sub_n)
                            }
                        }
                    } else {
                        Self::delete_in_node(tree, key, hash, level+1, sub_slot, sub_n)
                    }
                }
            }
        } else {
            None
        }
    }
    fn insert(&mut self, key: K, val: V) {
        let hash = Self::hash(key, self.seed);
        Self::insert_into_node(&mut self.root, key, val, hash, 0)
    }
    fn get(&self, key: K) -> Option<V> {
        let hash = Self::hash(key, self.seed);
        Self::lookup_in_node(&self.root, key, hash, 0)
    }
    fn remove(&mut self, key: K) -> Option<V> {
        let hash = Self::hash(key, self.seed);
        let slot = Self::get_slot(hash, 0);
        let n = Self::choose_child(&self.root, slot);
        Self::delete_in_node(&mut self.root, key, hash, 0, slot, n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type TestHamt<'a> = Hamt<&'a str, u64>;

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
            assert_eq!(b64::get(hamt.root.occupied, i), i == slot);
        }
        // Check children
        assert_eq!(hamt.root.children.len(), 1);
        assert_eq!(*hamt.root.children.first().unwrap(),
                   Child::KVPair("peter", 2));

        // Update value
        hamt.insert("peter", 5);
        // Check occupied bit
        for i in 0..N_CHILDREN {
            assert_eq!(b64::get(hamt.root.occupied, i), i == slot);
        }
        // Check children
        assert_eq!(hamt.root.children.len(), 1);
        assert_eq!(*hamt.root.children.first().unwrap(),
                   Child::KVPair("peter", 5));

        // Insert second kv pair
        hamt.insert("david", 5);
        let hash2 = TestHamt::hash("david", hamt.seed);
        let slot2 = TestHamt::get_slot(hash2, 0);
        // Check occupied bit
        for i in 0..N_CHILDREN {
            assert_eq!(b64::get(hamt.root.occupied, i),
                       i == slot || i == slot2,
                       "i={}, occupieds={:b}, slot1={}, slot2={}",
                       i, hamt.root.occupied, slot, slot2);
        }
        // Check children
        assert_eq!(hamt.root.children.len(), 2);
        assert!(hamt.root.children.contains(&Child::KVPair("peter", 5)));
        assert!(hamt.root.children.contains(&Child::KVPair("david", 5)));

        // Update peter again
        hamt.insert("peter", 3);
        // Check occupied bit
        for i in 0..N_CHILDREN {
            assert_eq!(b64::get(hamt.root.occupied, i), i == slot || i == slot2);
        }
        // Check children
        assert_eq!(hamt.root.children.len(), 2);
        assert!(hamt.root.children.contains(&Child::KVPair("peter", 3)));
        assert!(hamt.root.children.contains(&Child::KVPair("david", 5)));
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
        for (k,v) in kvs.iter() {
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
}

fn main() {

}