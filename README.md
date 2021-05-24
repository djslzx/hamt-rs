# hamt-rs
A Rust HAMT implementation

## Contributors
Andrew Thai, David Lee, Peter Zhao

## Overview
Implement a Hamt, a trie data structure, in Rust.
A HAMT is a hash array mapped trie; HAMTs are often used in functional programming languages (e.g. Clojure, Haskell).
 
## Project Goals
- Learn Rust, a modern systems programming language.
- Learn about Hamts.
- Implement a non-trivial tree data structure that uses hashing in Rust.

## Description of Project Deliverables
A compiling Rust repository containing
- Hamt implementation
- Writeup describing core concepts and implementation details
- Readme explaining usage
- Tests

## List of Milestones
1. Learn Rust (Rust Book)
    - [Hazard Pointers](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.112.6406&rep=rep1&type=pdf)
2. Describe and understand Hamt interface, algorithms, and API
3. Implement Hamt
4. Testing
    - Correctness tests: Does Hamt behave as expected and satisfy key features?
        - Test API operations
        - Atomicity, Linearizability, lock-freedom
    - Performance tests: If time permits, compare against another [Rust implementation](https://github.com/ballard26/concurrent-hamt)
        - NOTE: We will not be using this for reference until we have completed our implementation
6. Writeup (short)
    - Explain algorithm
    - Describe key aspects of our implementation + simplifications we make
    - Testing results + performance
7. ???
8. Profit!

## Timeline
- 5/8  - Meet to discuss what we've read
- 5/9  - Learn Rust + Read Papers
- 5/19 - Implementation
- 5/23 - Submission
