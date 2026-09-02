
use divan::{Divan, Bencher, black_box};
use pathmap::PathMap;

use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

fn main() {
    // Run registered benchmarks.
    let divan = Divan::from_args()
        .sample_count(5);

    divan.main();
}

/// Call with `as_words == true` for a separate entry for each word, pass false for an entry for each sentence (clause)
fn read_data(as_words: bool) -> Vec<String> {

    //The complete works of Shakespeare can be downloaded as a single file here:
    // https://ocw.mit.edu/ans7870/6/6.006/s08/lecturenotes/files/t8.shakespeare.txt
    // ~200k clauses
    // ~900k words
    let data_dir = match std::env::var("BENCH_DATA_DIR") {
        Ok(val) => std::path::PathBuf::from(val),
        Err(_) => std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benches"),
    };
    let file_path = data_dir.join("shakespeare.txt");
    let file = File::open(file_path).unwrap();

    //Parse the file, with each sentence clause as an expression
    let mut reader = BufReader::new(file);
    let mut line = String::new();
    let mut strings = vec![];
    while reader.read_line(&mut line).unwrap() > 0 {

        const TERMINATORS: &[char] = &[',', '.', ';', '?', '\"', '-', '[', ']'];
        const SEPARATORS: &[char] = &[' ', '\t', '\n'];
        const IGNORE_CHARS: &[char] = &['\''];

        for clause in line.split_inclusive(TERMINATORS) {
            if as_words {
                for sym in clause.split(SEPARATORS) {
                    let ignore_chars = [TERMINATORS, IGNORE_CHARS].concat();
                    let sym = sym.replace(&ignore_chars[..], "");

                    if sym.len() > 0 {
                        strings.push(sym);
                    }
                }
            } else {
                strings.push(clause.to_owned());
            }
        }
        line.clear();
    }

    strings
}

#[divan::bench()]
fn shakespeare_words_insert(bencher: Bencher) {

    let strings = read_data(true);

    bencher.bench_local(|| {
        let mut map = PathMap::new();
        for (v, k) in strings.iter().enumerate() {
            map.set_val_at(k, v);
        }
    });
}

#[divan::bench()]
fn shakespeare_words_get(bencher: Bencher) {

    let strings = read_data(true);
    let mut map = PathMap::new();
    for (v, k) in strings.iter().enumerate() {
        map.set_val_at(k, v);
    }

    // let counters = pathmap::counters::Counters::count_ocupancy(&map);
    // // counters.print_histogram_by_depth();
    // counters.print_run_length_histogram();

    let mut _map_v = 0;
    bencher.bench_local(|| {
        for k in strings.iter() {
            *black_box(&mut _map_v) = *map.get_val_at(k).unwrap();
            //Annoyingly, we can't check for the correct value because so many places share a name
            //assert_eq!(map.get_val_at(k), Some(&v));
        }
    });
}

#[divan::bench()]
fn shakespeare_words_val_count(bencher: Bencher) {

    let strings = read_data(true);
    let mut map = PathMap::new();
    let mut unique_count = 0;
    for (v, k) in strings.iter().enumerate() {
        if map.set_val_at(k, v).is_none() {
            unique_count += 1;
        }
    }

    let mut sink = 0;
    bencher.bench_local(|| {
        *black_box(&mut sink) = map.val_count();
    });
    assert_eq!(sink, unique_count);
}

#[divan::bench()]
fn shakespeare_sentences_insert(bencher: Bencher) {

    let strings = read_data(false);

    bencher.bench_local(|| {
        let mut map = PathMap::new();
        for (v, k) in strings.iter().enumerate() {
            map.set_val_at(k, v);
        }
    });
}

#[divan::bench()]
fn shakespeare_sentences_get(bencher: Bencher) {

    let strings = read_data(false);
    let mut map = PathMap::new();
    for (v, k) in strings.iter().enumerate() {
        map.set_val_at(k, v);
    }

    // let counters = pathmap::counters::Counters::count_ocupancy(&map);
    // // counters.print_histogram_by_depth();
    // counters.print_run_length_histogram();

    let mut _map_v = 0;
    bencher.bench_local(|| {
        for k in strings.iter() {
            *black_box(&mut _map_v) = *map.get_val_at(k).unwrap();
            //Annoyingly, we can't check for the correct value because so many places share a name
            //assert_eq!(map.get_val_at(k), Some(&v));
        }
    });
}

#[divan::bench()]
fn shakespeare_sentences_val_count(bencher: Bencher) {

    let strings = read_data(false);
    let mut map = PathMap::new();
    let mut unique_count = 0;
    for (v, k) in strings.iter().enumerate() {
        if map.set_val_at(k, v).is_none() {
            unique_count += 1;
        }
    }

    let mut sink = 0;
    bencher.bench_local(|| {
        *black_box(&mut sink) = map.val_count();
    });
    assert_eq!(sink, unique_count);
}

#[cfg(feature="arena_compact")]
#[divan::bench()]
fn shakespeare_sentences_val_count_act(bencher: Bencher) {
    use pathmap::{
        arena_compact::ArenaCompactTree,
        zipper::ZipperMoving,
    };
    let strings = read_data(false);
    let mut map = PathMap::new();
    let mut unique_count = 0;
    for (v, k) in strings.iter().enumerate() {
        if map.set_val_at(k, v).is_none() {
            unique_count += 1;
        }
    }
    let act = ArenaCompactTree::from_zipper(map.read_zipper(), |&v| v as u64);
    let act_zipper = act.read_zipper();
    let mut sink = 0;
    bencher.bench_local(|| {
        *black_box(&mut sink) = act_zipper.val_count();
    });
    assert_eq!(sink, unique_count);
}
