// Fast assembly rank and select
#[allow(unused_assignments)]
pub fn popcnt(val: u64) -> u64 {
    unsafe {
        let mut o: u64 = 0;
        asm!("popcnt {0}, {1}",
        out(reg) o,
        in(reg) val,
        options(preserves_flags),
        );
        o
    }
}

/// Count the number of 1 bits in val[0, pos]
pub fn bitrank(val: u64, pos: usize) -> u64 {
    let mask = 2 << pos; // 2^(pos+1)
    let mask = if mask == 0 { !0 } else { mask-1 };
    let val = val & mask;
    popcnt(val)
}
// val = 010100, pos = 2
// mask = 000010 --> 001000
// mask = 000111
// val = 000100 -> popcnt this = 1 which is wrong, we want to insert in index 0 (popcnt up to i EXCLUSIVELY)

pub mod bitarr {
    // 64-bit bit arrays
    pub mod b64 {
        pub fn get(x: u64, at: usize) -> bool {
            debug_assert!(at < 64);
            (x & (1 << at)) != 0
        }
        pub fn set(x: u64, at: usize) -> u64 {
            x | (1 << at)
        }
        pub fn unset(x: u64, at: usize) -> u64 {
            x & !(1 << at)
        }
        pub fn set_to(x: u64, on: bool, at: usize) -> u64 {
            debug_assert!(at < 64);
            if on {
                self::set(x, at)
            } else {
                self::unset(x, at)
            }
        }
        /// Get the position of the highest set bit in `x`
        pub fn highest_set_bit(x: u64) -> usize {
            debug_assert_ne!(x, 0);
            63 - (x.leading_zeros() as usize)
        }
        /// Get a bitmask where bits in [0, i-1] are set and all other bits are unset
        pub fn mask(i: usize) -> u64 {
            debug_assert!(i < 64);
            (1 << i) - 1
        }
        #[cfg(test)]
        mod tests {
            use super::*;

            #[test]
            fn test_b64_get() {
                let zeros = 0_u64;
                let ones = !0_u64;
                for i in 0..64 {
                    assert_eq!(get(zeros, i), false, "i={}", i);
                    assert_eq!(get(ones, i), true, "i={}", i);
                }
                assert_eq!(get(0b1101_1001_1000, 0), false);
                assert_eq!(get(0b1101_1001_1000, 1), false);
                assert_eq!(get(0b1101_1001_1000, 2), false);
                assert_eq!(get(0b1101_1001_1000, 3), true);
                assert_eq!(get(0b1101_1001_1000, 4), true);
                assert_eq!(get(0b1101_1001_1000, 5), false);
                assert_eq!(get(0b1101_1001_1000, 6), false);
                assert_eq!(get(0b1101_1001_1000, 7), true);
                assert_eq!(get(0b1101_1001_1000, 8), true);
                assert_eq!(get(0b1101_1001_1000, 9), false);
                assert_eq!(get(0b1101_1001_1000, 10), true);
                assert_eq!(get(0b1101_1001_1000, 11), true);
            }

            #[test]
            fn test_b64_set() {
                // 0 -> 1
                assert_eq!(set(0, 0), 1);
                assert_eq!(set(0, 1), 2);
                assert_eq!(set(0, 2), 4);
                assert_eq!(set(0, 4), 16);
                assert_eq!(set(0, 63), 1 << 63);
                // 0 -> 0
                assert_eq!(set(!0, 0), !0);
                assert_eq!(set(!0, 4), !0);
                assert_eq!(set(!0, 63), !0);
            }

            #[test]
            fn test_unset() {
                let ones = !0_u64;
                let zeros = 0_u64;
                for i in 0..64 {
                    assert_eq!(unset(ones, i), !(1 << i));
                    assert_eq!(unset(zeros, i), zeros);
                }
            }

            #[test]
            fn test_set_to() {
                let zeros = 0_u64;
                let ones = !0_u64;
                for i in 0..64 {
                    assert_eq!(set_to(zeros, true, i), 1 << i, "i={}", i);
                    assert_eq!(set_to(zeros, false, i), 0, "i={}", i);
                    assert_eq!(set_to(ones, true, i), !0, "i={}", i);
                    assert_eq!(set_to(ones, false, i), !(1 << i), "i={}", i);
                }
            }

            #[test]
            fn test_highest_set_bit() {
                // One set bit at i
                for i in 0..64 {
                    assert_eq!(highest_set_bit(1 << i), i)
                }
                // Two set bits
                for i in 0..64 {
                    for j in i + 1..64 {
                        assert_eq!(highest_set_bit((1 << i) | (1 << j)), j)
                    }
                }
            }
        }
    }
    // 128-bit bit arrays
    pub mod b128 {
        /// Bits in [a,b) set to 1, others set to 0;
        /// Indexing from right (LSB has index 0)
        pub fn half_open(a: usize, b: usize) -> u128 {
            debug_assert!(a <= b, "({}, {}]", a, b);
            if a == b {
                0
            } else if b - a == 128 {
                !0
            } else {
                ((1 << (b - a)) - 1) << a
            }
        }
        /// Bits in [a,b] set to 1, others set to 0
        /// Indexing from right (LSB has index 0)
        pub fn closed(a: usize, b: usize) -> u128 {
            self::half_open(a, b + 1)
        }
        pub fn mask(k: usize) -> u128 {
            (1 << k) - 1
        }
        /// Get bits in [a, b) and place in [0, b-a)
        pub fn get_bits(x: u128, a: usize, b:usize) -> u128 {
            (x & half_open(a, b)) >> a
        }
        #[cfg(test)]
        mod tests {
            use super::*;

            #[test]
            fn test_half_open() {
                assert_eq!(half_open(0, 1), 1, "{:x}", half_open(0, 1));
                assert_eq!(half_open(127, 128), 1 << 127, "{:x}", half_open(127, 128));
                assert_eq!(half_open(0, 128), !0, "{:x}", half_open(0, 128));
                assert_eq!(half_open(1, 128), !1, "{:x}", half_open(1, 128));
                assert_eq!(half_open(0, 127), !(1 << 127), "{:x}", half_open(0, 127));
                assert_eq!(half_open(1, 127), !0 << 2 >> 1, "{:x}", half_open(1, 128));
            }
            #[test]
            fn test_closed() {
                assert_eq!(closed(0, 0), 1, "{:x}", closed(0, 0));
                assert_eq!(closed(127, 127), 1 << 127, "{:x}", closed(127, 127));
                assert_eq!(closed(0, 127), !0, "{:x}", closed(0, 127));
                assert_eq!(closed(1, 127), !1, "{:x}", closed(1, 127));
                assert_eq!(closed(0, 126), !(1 << 127), "{:x}", closed(0, 126));
                assert_eq!(closed(1, 126), !0 << 2 >> 1, "{:x}", closed(1, 126));
            }
            #[test]
            fn test_ones() {
                for i in 0..64 {
                    assert_eq!(mask(i), half_open(0, i));
                }
            }
            #[test]
            fn test_get_bits() {
                assert_eq!(get_bits(0b0, 0, 0), 0);
                assert_eq!(get_bits(0b1, 0, 1), 1);
                assert_eq!(get_bits(0b10, 0, 1), 0);
                assert_eq!(get_bits(0b10, 1, 2), 1);
                assert_eq!(get_bits(0b1010, 1, 4), 0b101);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_popcnt() {
        assert_eq!(popcnt(0b0), 0);
        assert_eq!(popcnt(0b1), 1);
        assert_eq!(popcnt(0b101010), 3);
    }

    #[test]
    fn test_bitrank() {
        for i in 0..=63 {
            for j in 0..=63 {
                assert_eq!(
                    bitrank(1 << i, j),
                    if i <= j { 1 } else { 0 },
                    "i={}, j={}", i, j,
                );
            }
        }
    }
}