use std::collections::BTreeSet;

use pathmap::PathMap;

type KeySet = BTreeSet<Vec<u8>>;

fn next_u64(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    *state
}

fn fixed_width_set(seed: u64, salt: u64) -> KeySet {
    let mut state = seed ^ salt;
    let mut keys = KeySet::new();
    for ordinal in 0..72_u64 {
        let mut key = vec![0_u8; 8];
        for byte in &mut key {
            *byte = (next_u64(&mut state) >> 32) as u8;
        }
        key[0] ^= ordinal as u8;
        keys.insert(key);
    }
    keys
}

fn prefix_heavy_set(seed: u64, salt: u64) -> KeySet {
    let mut state = seed ^ salt;
    let mut keys = KeySet::new();
    if next_u64(&mut state) & 7 == 0 {
        keys.insert(Vec::new());
    }
    for index in 0..48_u8 {
        let length = (next_u64(&mut state) % 9) as usize;
        let mut key = Vec::with_capacity(length);
        for position in 0..length {
            let selector = next_u64(&mut state);
            key.push(match selector % 5 {
                0 => index,
                1 => position as u8,
                2 => (selector >> 32) as u8,
                3 => b'a' + (selector % 7) as u8,
                _ => 0xff_u8.wrapping_sub(index),
            });
        }
        keys.insert(key.clone());
        if key.len() > 1 && index % 3 == 0 {
            keys.insert(key[..key.len() - 1].to_vec());
        }
        if index % 7 == 0 {
            key.extend_from_slice(&[0, index]);
            keys.insert(key);
        }
    }
    keys
}

fn map_from_set(keys: &KeySet) -> PathMap<()> {
    let mut map = PathMap::new();
    for key in keys {
        map.insert(key, ());
    }
    map
}

fn set_from_map(map: &PathMap<()>) -> KeySet {
    map.iter().map(|(key, ())| key).collect()
}

#[test]
fn seeded_prefix_free_algebra_matches_btreeset_oracle() {
    for seed in 0_u64..256 {
        let a = fixed_width_set(seed, 0x243f_6a88_85a3_08d3);
        let b = fixed_width_set(seed, 0x1319_8a2e_0370_7344);
        let c = fixed_width_set(seed, 0xa409_3822_299f_31d0);
        let ma = map_from_set(&a);
        let mb = map_from_set(&b);
        let mc = map_from_set(&c);

        let union = a.union(&b).cloned().collect::<KeySet>();
        let intersection = a.intersection(&b).cloned().collect::<KeySet>();
        let difference = a.difference(&b).cloned().collect::<KeySet>();
        assert_eq!(set_from_map(&ma.join(&mb)), union, "join seed {seed}");
        assert_eq!(
            set_from_map(&ma.meet(&mb)),
            intersection,
            "meet seed {seed}"
        );
        assert_eq!(
            set_from_map(&ma.subtract(&mb)),
            difference,
            "subtract seed {seed}"
        );

        assert_eq!(set_from_map(&ma.join(&mb)), set_from_map(&mb.join(&ma)));
        assert_eq!(set_from_map(&ma.meet(&mb)), set_from_map(&mb.meet(&ma)));
        assert_eq!(set_from_map(&ma.join(&ma)), a);
        assert_eq!(set_from_map(&ma.meet(&ma)), a);
        assert!(set_from_map(&ma.subtract(&ma)).is_empty());
        assert_eq!(
            set_from_map(&ma.join(&mb).join(&mc)),
            set_from_map(&ma.join(&mb.join(&mc)))
        );
        assert_eq!(
            set_from_map(&ma.meet(&mb).meet(&mc)),
            set_from_map(&ma.meet(&mb.meet(&mc)))
        );
        assert_eq!(
            set_from_map(&ma.meet(&mb.join(&mc))),
            set_from_map(&ma.meet(&mb).join(&ma.meet(&mc)))
        );
    }
}

#[test]
fn cloned_prefix_heavy_maps_are_logically_isolated_under_mutation() {
    for seed in 0_u64..128 {
        let original_set = prefix_heavy_set(seed, 0x082e_fa98_ec4e_6c89);
        let original = map_from_set(&original_set);
        let mut changed = original.clone();
        let removed = original_set.iter().next().cloned();
        if let Some(key) = &removed {
            assert!(changed.remove(key).is_some());
        }
        let inserted = vec![0xfe, (seed >> 8) as u8, seed as u8, 0x01];
        changed.insert(&inserted, ());
        assert_eq!(
            set_from_map(&original),
            original_set,
            "original seed {seed}"
        );
        let mut expected = original_set;
        if let Some(key) = removed {
            expected.remove(&key);
        }
        expected.insert(inserted);
        assert_eq!(set_from_map(&changed), expected, "clone seed {seed}");
    }
}

#[test]
fn prefix_valued_meet_is_associative_seed_44() {
    let seed = 44;
    let a = map_from_set(&prefix_heavy_set(seed, 0x243f_6a88_85a3_08d3));
    let b = map_from_set(&prefix_heavy_set(seed, 0x1319_8a2e_0370_7344));
    let c = map_from_set(&prefix_heavy_set(seed, 0xa409_3822_299f_31d0));
    assert_eq!(
        set_from_map(&a.meet(&b).meet(&c)),
        set_from_map(&a.meet(&b.meet(&c)))
    );
}

#[test]
fn seeded_prefix_heavy_dual_distributivity_matches_btreeset_oracle() {
    // Seeds 10, 77, and 287 are focused regressions for CoFree identity
    // operand selection and mixed value/onward-link exhaustiveness.
    for seed in 0_u64..512 {
        let a = prefix_heavy_set(seed, 0x243f_6a88_85a3_08d3);
        let b = prefix_heavy_set(seed, 0x1319_8a2e_0370_7344);
        let c = prefix_heavy_set(seed, 0xa409_3822_299f_31d0);
        let ma = map_from_set(&a);
        let mb = map_from_set(&b);
        let mc = map_from_set(&c);

        let b_meet_c = b.intersection(&c).cloned().collect::<KeySet>();
        let expected = a.union(&b_meet_c).cloned().collect::<KeySet>();

        assert_eq!(
            set_from_map(&ma.join(&mb.meet(&mc))),
            expected,
            "left dual-distributive form seed {seed}"
        );
        assert_eq!(
            set_from_map(&ma.join(&mb).meet(&ma.join(&mc))),
            expected,
            "right dual-distributive form seed {seed}"
        );
    }
}
