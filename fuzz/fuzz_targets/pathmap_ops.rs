#![no_main]
use libfuzzer_sys::fuzz_target;
use pathmap::PathMap;
use arbitrary::Arbitrary;
use std::collections::HashMap;

#[derive(Arbitrary, Debug)]
enum Op {
    Insert { key: Vec<u8>, val: u8 },
    Remove { key: Vec<u8> },
    Get { key: Vec<u8> },
    CheckLen,
}

fuzz_target!(|ops: Vec<Op>| {
    let mut map = PathMap::new();
    let mut model = HashMap::new();

    for op in ops {
        match op {
            Op::Insert { key, val } => {
                map.insert(&key, val);
                model.insert(key, val);
            },
            Op::Remove { key } => {
                let res = map.remove(&key);
                let model_res = model.remove(&key);
                assert_eq!(res, model_res, "Remove mismatch for key: {:?}", key);
            },
            Op::Get { key } => {
                let res = map.get(&key).copied();
                let model_res = model.get(&key).copied();
                assert_eq!(res, model_res, "Get mismatch for key: {:?}", key);
            },
            Op::CheckLen => {
                // Note: PathMap::val_count() might be O(N), so use sparingly in heavy fuzzing
                // but good for correctness checks.
                assert_eq!(map.val_count(), model.len(), "Length mismatch");
                assert_eq!(map.is_empty(), model.is_empty(), "Empty mismatch");
            }
        }
    }
});
