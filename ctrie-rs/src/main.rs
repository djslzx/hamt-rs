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
    hash::{Hash}
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
    fn insert_into_node(node: &mut Tree<K,V>, key: K, val: V, seed: u32) {
        let hash = Self::hash(key, seed);
        let slot = (hash & b128::mask(LOG_N_CHILDREN)) as usize;
        let n: usize = if slot == 0 {0} else {bitrank(node.occupied, slot-1)} as usize;
        if b64::get(node.occupied, slot) {
            match node.children.get_mut(n).unwrap() {
                Child::KVPair(k, v) => {
                    if *k == key {
                        // if occupied by entry with the same key, update value
                        *v = val;
                    } else {
                        // if occupied by entry with different key, replace with subtree
                        let mut subtree = Tree::new();
                        Self::insert_into_node(&mut subtree, *k, *v, seed);
                        Self::insert_into_node(&mut subtree, key, val, seed);
                        node.children.insert(n, Child::AMTNode(subtree));
                    }
                }
                Child::AMTNode(tree) => {
                    // if subtree, then enter subtree and recursively insert
                    Self::insert_into_node(tree, key, val, seed);
                }
            }
        } else {
            // add the k-v pair, set occupied
            node.occupied = b64::set(node.occupied, slot);
            node.children.insert(n, Child::KVPair(key, val));
        }
    }
    fn insert(&mut self, key: K, val: V) {
        Self::insert_into_node(&mut self.root, key, val, self.seed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type TestHamt<'a> = Hamt<&'a str, u64>;

    fn get_slot(hamt: &TestHamt, key: &str) -> usize {
        let hash = TestHamt::hash(key, hamt.seed);
        (hash & b128::mask(LOG_N_CHILDREN)) as usize
    }

    #[test]
    fn test_insert() {
        let mut hamt = Hamt::new();
        // First insert
        hamt.insert("peter", 2);
        let slot = get_slot(&hamt, "peter");
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
        let slot2 = get_slot(&hamt, "david");
        // Check occupied bit
        for i in 0..N_CHILDREN {
            assert_eq!(b64::get(hamt.root.occupied, i), i == slot || i == slot2);
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
}

fn main() {

}