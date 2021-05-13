#![feature(asm)]
#![allow(dead_code)]

mod util;
use crate::util::{
    bitrank,
    bitarr::{
        b64, b128,
    },
};
use std::hash::{Hash};
use fasthash::murmur3::hash128_with_seed;

// Structs
#[derive(Debug)]
pub struct Tree<K, V> where K: Hash {
    occupied: u64,
    children: Vec<Child<K,V>>,
    seed: u32,
}

#[derive(Debug)]
enum Child<K,V> where K: Hash {
    Pair(K, V),
    AMTNode(Tree<K, V>),
}

impl<K: Clone,V> Tree<K, V> where K: Hash + AsRef<[u8]> + PartialEq {
    fn hash(&self, key: K) -> u128 {
        hash128_with_seed(key, self.seed)
    }
    fn insert(&mut self, key: K, val: V) {
        // do hash
        let h = self.hash(key.clone());
        let i = (h & b128::mask(6)) as usize;
        println!("h: 0x{:x}, i: 0x{:x}", h, i);

        // try looking at appropriate entry
        let mut n = bitrank(self.occupied, i) as usize;
        println!("bitmap: {:b}", self.occupied);
        // TODO: Bitrank is weird on same keys/collisions. Need to check
        println!("n: {}", n);
        // if n > 0 {
        //     n -= 1;
        // }
        // 000000 -> 0
        // 100000 -> 0
        if b64::get(self.occupied, i) {
            match self.children.get(n).unwrap() {
                Child::Pair(_, _) => {
                
                    // TODO: Is this most efficient way of getting ownership of matched var?
                    if let Child::Pair(old_k, old_v) = self.children.remove(n) {
                        if old_k == key {
                            self.children.insert(n, Child::Pair(key, val));
                        } else {
                            // if occupied by entry with different key, then make subtree
                            let mut subtree = Tree {
                                occupied: 0,
                                children: Vec::new(),
                                seed: 0,
                            };
                            subtree.insert(old_k, old_v);   
                            subtree.insert(key, val);      
                            self.children.insert(n, Child::AMTNode(subtree));   
                        }                                                            
                    }   
                             
                }
                Child::AMTNode(_) => {
                    // if subtree, then enter subtree and recursively insert
                    if let Child::AMTNode(mut tree) = self.children.remove(n) {
                        tree.insert(key, val);
                        self.children.insert(n, Child::AMTNode(tree));
                    }                    
                }
            }
        } else {
            // add the k-v pair, set occupied
            self.occupied = b64::set(self.occupied, i);
            self.children.insert(n, Child::Pair(key, val));
        }
    }
}

fn main() {
    let mut tree = Tree {
        occupied: 0,
        children: Vec::new(),
        seed: 0,
    };
    tree.insert("peter", 2);
    println!("{:?}", tree);
    tree.insert("peter", 5);
    println!("{:?}", tree);
    tree.insert("andrew", 3);
    println!("{:?}", tree);
    tree.insert("david", 4);
    println!("{:?}", tree);
    tree.insert("andrew", 11);
    println!("{:?}", tree);
    tree.insert("peter", 6);
    println!("{:?}", tree);
    tree.insert("david", 10);
    println!("{:?}", tree);
}