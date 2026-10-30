//! Traces some small programs, replays them, and checks the replay matches what really happened.  Each
//! test writes its animation to the test's temporary directory.  Run with `--nocapture` to see the paths

use std::io::{self, Write};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use pathmap::PathMap;
use pathmap::arena_compact::ArenaCompactTree;
use pathmap::utils::debug::zipper_tracing::{TraceTarget, TraceZipper, decode_trace};
use pathmap::zipper::*;
use tracer::{render_html, replay, Annotations, Replay, ReplayConfig};


#[derive(Clone, Default)]
struct SharedBuf(Arc<Mutex<Vec<u8>>>);

impl Write for SharedBuf {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> { self.0.lock().unwrap().extend_from_slice(buf); Ok(buf.len()) }
    fn flush(&mut self) -> io::Result<()> { Ok(()) }
}

/// Runs `f` with a trace open, and returns the trace
fn traced(f: impl FnOnce(&TraceTarget)) -> Vec<u8> {
    let buf = SharedBuf::default();
    let target = TraceTarget::new::<u64>(buf.clone()).unwrap();
    f(&target);
    target.close().unwrap();
    let bytes = buf.0.lock().unwrap().clone();
    bytes
}

fn out_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("tracer")
}

/// Replays the trace, and writes it as `name.trace` and its animation as `name.html`, with the annotations
/// in `tests/name.ann.json` if there are any
fn replay_and_render(name: &str, trace: &[u8], seeds: Vec<(String, PathMap<u64>)>) -> Replay<u64> {
    let events = decode_trace::<u64>(trace).unwrap();
    let replay = replay(&events, seeds, &ReplayConfig::default());
    assert!(replay.warnings.is_empty(), "{:?}", replay.warnings);
    std::fs::create_dir_all(out_dir()).unwrap();
    std::fs::write(out_dir().join(format!("{name}.trace")), trace).unwrap();
    let path = out_dir().join(format!("{name}.html"));
    let ann_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests").join(format!("{name}.ann.json"));
    let ann = ann_path.exists().then(|| Annotations::from_json(&std::fs::read_to_string(&ann_path).unwrap()).unwrap());
    std::fs::write(&path, render_html(&replay, name, ann.as_ref()).unwrap()).unwrap();
    println!("{name}: {}", path.display());
    replay
}

fn entries(map: &PathMap<u64>) -> Vec<(Vec<u8>, u64)> {
    map.iter().map(|(path, val)| (path, *val)).collect()
}

#[test]
fn one_zipper_assembles_paths() {
    let mut map = PathMap::<u64>::new();
    let trace = traced(|target| {
        let mut wz = TraceZipper::with_id(1, map.write_zipper(), target.clone());
        //The zipper's path runs past the trie until a value is set at the end of it
        for &byte in b"hello" {
            wz.descend_to_byte(byte);
        }
        wz.set_val(1);
        wz.ascend(2);
        wz.descend_to_byte(b'p');
        wz.set_val(2);
        wz.ascend(1);
        wz.descend_to(b"icopter");
        wz.set_val(3);
        wz.reset();
        wz.descend_to(b"hi");
        wz.set_val(4);
        wz.ascend(1);
        wz.descend_to(b"el");
        //Removes "help", "hello", and "helicopter"
        wz.remove_branches(true);
        wz.reset();
    });
    let replay = replay_and_render("one_zipper", &trace, vec![]);
    assert_eq!(replay.maps.len(), 1);
    assert_eq!(entries(&replay.maps[0]), entries(&map));
    assert_eq!(entries(&map), vec![(b"hi".to_vec(), 4)]);

    //Partway through descending "hello", "hel" exists only as the zipper's path
    let frame = &replay.frames[4];
    let nodes = &frame.maps[0].nodes;
    assert!(!nodes[&b"hel"[..]].exists);
    assert_eq!(frame.maps[0].zippers[0].focus, b"hel");
    //Once the value is set, the whole path exists
    let frame = &replay.frames[7];
    assert!(frame.maps[0].nodes[&b"hello"[..]].exists);
    assert_eq!(frame.maps[0].nodes[&b"hello"[..]].val.as_deref(), Some("1"));
}

#[test]
fn two_zipper_dance() {
    let mut map = PathMap::<u64>::new();
    let trace = traced(|target| {
        let zh = map.zipper_head();
        let mut a = TraceZipper::with_id(1, zh.write_zipper_at_exclusive_path(b"ab/x/").unwrap(), target.clone());
        let mut b = TraceZipper::with_id(2, zh.write_zipper_at_exclusive_path(b"ab/y/").unwrap(), target.clone());
        //The two writers take turns building words in their own regions
        for (val, (a_word, b_word)) in [("cat", "dog"), ("car", "dot"), ("cart", "do")].into_iter().enumerate() {
            a.descend_to(a_word);
            a.set_val(val as u64);
            a.reset();
            b.descend_to(b_word);
            b.set_val(10 + val as u64);
            b.reset();
        }
        drop(b);
        //A reader walks the values the second writer left behind
        let mut r = TraceZipper::with_id(3, zh.read_zipper_at_path(b"ab/y/").unwrap(), target.clone());
        while r.to_next_val() {}
        r.reset();
        r.descend_to(b"do");
        //The first writer grafts a copy of what the reader sees
        a.descend_to(b"copy/");
        a.graft(&r);
        drop(r);
        drop(a);
    });
    let replay = replay_and_render("two_zipper_dance", &trace, vec![]);
    //Both writers' roots start with "ab", so they share a map
    assert_eq!(replay.maps.len(), 1);
    assert_eq!(entries(&replay.maps[0]), entries(&map));
    assert_eq!(map.get(b"ab/x/copy/g"), Some(&10));
    let graft = replay.frames.iter().find(|frame| frame.caption.contains(".graft(")).unwrap();
    assert_eq!(graft.sources, vec![3]);
    //After z2 is dropped, what it wrote is still shown, though no zipper can reach it
    let dropped = replay.frames.iter().find(|frame| frame.caption == "z2.drop()").unwrap();
    let dog = &dropped.maps[0].nodes[&b"ab/y/dog"[..]];
    assert!(dog.exists && !dog.accessible);
    assert_eq!(dog.val.as_deref(), Some("10"));
    assert!(dropped.maps[0].nodes[&b"ab/x/"[..]].accessible);
}

#[test]
fn act_seeded_replay() {
    let mut map: PathMap<u64> = [("apple", 1), ("apricot", 2), ("banana", 3), ("band", 4)].into_iter().collect();
    std::fs::create_dir_all(out_dir()).unwrap();
    let act_path = out_dir().join("seed.act");
    ArenaCompactTree::dump_from_zipper(map.read_zipper(), |val: &u64| *val, &act_path).unwrap();
    let trace = traced(|target| {
        let mut rz = TraceZipper::with_id(1, map.read_zipper(), target.clone());
        while rz.to_next_val() {}
        drop(rz);
        let mut wz = TraceZipper::with_id(2, map.write_zipper(), target.clone());
        wz.descend_to(b"ban");
        wz.remove_branches(true);
        wz.reset();
        wz.descend_to(b"ap");
        wz.descend_until();
    });
    let seed = tracer::load_act::<u64>(&act_path).unwrap();
    let replay = replay_and_render("act_seeded", &trace, vec![("seed.act".to_string(), seed)]);
    //Both zippers are at the root, which every seed contains, so both are on the seeded map
    assert_eq!(replay.maps.len(), 1);
    assert_eq!(entries(&replay.maps[0]), entries(&map));
    //The reader sees the seeded contents
    assert!(replay.frames[2].maps[0].nodes[&b"ap"[..]].exists);
}

#[test]
fn wide_trie() {
    let mut map = PathMap::<u64>::new();
    let trace = traced(|target| {
        //More children per node than are shown
        let mut wz = TraceZipper::with_id(1, map.write_zipper(), target.clone());
        for (idx, first) in (b'a'..=b'z').enumerate() {
            for second in b"xyz" {
                wz.set_val_at([first, *second], idx as u64);
            }
        }
        drop(wz);
        //Zippers at the root are on separate maps unless they reuse an id, so the reader reuses the writer's id
        let mut rz = TraceZipper::with_id(1, map.read_zipper(), target.clone());
        for _ in 0..4 {
            rz.to_next_val();
        }
        rz.reset();
        rz.descend_to(b"q");
    });
    let replay = replay_and_render("wide_trie", &trace, vec![]);
    assert_eq!(replay.maps.len(), 1);
    assert_eq!(entries(&replay.maps[0]), entries(&map));
    //The root has 26 children, but only 12 are shown.  The reader at "q" adds one more
    let last = replay.frames.iter().rev().find(|frame| frame.caption == "z1.descend_to(\"q\")").unwrap();
    assert_eq!(last.maps[0].nodes[&b""[..]].hidden, 26 - 13);
    assert!(!last.maps[0].zippers[0].writer);
}

/// A small version of the aunt query from MORK's aunt-kg benchmark.  Names are 3 bytes plus a separator,
/// so dropping the leading symbol of every path below a zipper is `join_k_path_into(4)`
#[test]
fn aunt_kg() {
    const PARENTS: [(&str, &str); 12] = [
        ("ann", "bob"), ("ann", "cat"), ("ann", "dee"), ("gus", "eve"), ("gus", "hal"), ("gus", "ivy"),
        ("bob", "jon"), ("bob", "kim"), ("eve", "jon"), ("eve", "kim"), ("dee", "lou"), ("hal", "max"),
    ];
    //lou's gender isn't recorded, so lou isn't a person
    const FEMALE: [&str; 6] = ["ann", "cat", "dee", "eve", "ivy", "kim"];
    const MALE: [&str; 5] = ["bob", "gus", "hal", "jon", "max"];
    const SYMBOL_LEN: usize = 4;

    let mut family = PathMap::<u64>::new();
    for (parent, child) in PARENTS {
        family.insert(format!("kg/parent/{parent}/{child}"), 1);
    }
    for person in FEMALE {
        family.insert(format!("kg/female/{person}"), 1);
    }
    for person in MALE {
        family.insert(format!("kg/male/{person}"), 1);
    }
    std::fs::create_dir_all(out_dir()).unwrap();
    let act_path = out_dir().join("family.act");
    ArenaCompactTree::dump_from_zipper(family.read_zipper(), |val: &u64| *val, &act_path).unwrap();

    let mut output = PathMap::<u64>::new();
    let trace = traced(|target| {
        let family_head = family.zipper_head();
        let output_head = output.zipper_head();

        //family |= (child $y $x) for each (parent $x $y)
        let mut parent = TraceZipper::with_id(1, family_head.read_zipper_at_path(b"kg/parent/").unwrap(), target.clone());
        let mut child_index = TraceZipper::with_id(2, family_head.write_zipper_at_exclusive_path(b"kg/child/").unwrap(), target.clone());
        while parent.to_next_val() {
            let fact = parent.path().to_vec();
            let (p, c) = fact.split_at(SYMBOL_LEN);
            child_index.descend_to(c);
            child_index.descend_to(b"/");
            child_index.descend_to(&p[..SYMBOL_LEN - 1]);
            child_index.set_val(1);
            child_index.reset();
        }
        drop(child_index);
        parent.reset();

        //person = female ∪ male
        let female = TraceZipper::with_id(3, family_head.read_zipper_at_path(b"kg/female/").unwrap(), target.clone());
        let male = TraceZipper::with_id(4, family_head.read_zipper_at_path(b"kg/male/").unwrap(), target.clone());
        let mut person_index = TraceZipper::with_id(5, family_head.write_zipper_at_exclusive_path(b"kg/person/").unwrap(), target.clone());
        person_index.graft(&female);
        let _ = person_index.join_into(&male);
        drop(person_index);
        drop(male);

        //Every person's parents
        let child = TraceZipper::with_id(6, family_head.read_zipper_at_path(b"kg/child/").unwrap(), target.clone());
        let mut person = TraceZipper::with_id(7, family_head.read_zipper_at_path(b"kg/person/").unwrap(), target.clone());
        let mut parents_out = TraceZipper::with_id(8, output_head.write_zipper_at_exclusive_path(b"out/parents/").unwrap(), target.clone());
        parents_out.graft(&child);
        let _ = parents_out.restrict(&person);
        drop(parents_out);

        //my_parents is positioned at the parents of each person in turn.  People without recorded parents are skipped
        let mut my_parents = TraceZipper::with_id(9, family_head.read_zipper_at_path(b"kg/child/").unwrap(), target.clone());
        let next_person = |person: &mut TraceZipper<_>, my_parents: &mut TraceZipper<_>| -> Option<Vec<u8>> {
            while person.to_next_val() {
                let mut dir = person.path().to_vec();
                dir.push(b'/');
                my_parents.move_to_path(&dir);
                if my_parents.path_exists() {
                    return Some(dir)
                }
            }
            None
        };

        //mother(p) = parents(p) ∩ female
        let mut mother_out = TraceZipper::with_id(10, output_head.write_zipper_at_exclusive_path(b"out/mother/").unwrap(), target.clone());
        while let Some(dir) = next_person(&mut person, &mut my_parents) {
            mother_out.move_to_path(&dir);
            let _ = mother_out.meet_2(&my_parents, &female);
        }
        drop(mother_out);
        person.reset();

        //sister(p) = (children of p's parents ∩ female) - p
        let mut sister_out = TraceZipper::with_id(11, output_head.write_zipper_at_exclusive_path(b"out/sister/").unwrap(), target.clone());
        while let Some(dir) = next_person(&mut person, &mut my_parents) {
            sister_out.move_to_path(&dir);
            sister_out.graft(&my_parents);
            sister_out.restricting(&parent);
            sister_out.join_k_path_into(SYMBOL_LEN, true);
            let _ = sister_out.meet_into(&female, true);
            if sister_out.descend_to_check(&dir[..SYMBOL_LEN - 1]) {
                sister_out.remove_val(true);
            }
        }
        drop(sister_out);
        person.reset();

        //aunt(p) = (children of p's grandparents - p's parents) ∩ female
        let mut aunt_out = TraceZipper::with_id(12, output_head.write_zipper_at_exclusive_path(b"out/aunt/").unwrap(), target.clone());
        while let Some(dir) = next_person(&mut person, &mut my_parents) {
            aunt_out.move_to_path(&dir);
            aunt_out.graft(&my_parents);
            aunt_out.restricting(&child);
            aunt_out.join_k_path_into(SYMBOL_LEN, true);
            if !aunt_out.restricting(&parent) {
                continue
            }
            aunt_out.join_k_path_into(SYMBOL_LEN, true);
            let _ = aunt_out.subtract_into(&my_parents, true);
            let _ = aunt_out.meet_into(&female, true);
        }
    });
    let seed = tracer::load_act::<u64>(&act_path).unwrap();
    let replay = replay_and_render("aunt_kg", &trace, vec![("family.act".to_string(), seed)]);
    //The family map is seeded, and the output map shares no prefix with it
    assert_eq!(replay.maps.len(), 2);
    assert_eq!(entries(&replay.maps[0]), entries(&family));
    assert_eq!(entries(&replay.maps[1]), entries(&output));
    let relation = |name: &str| -> Vec<String> {
        let prefix = format!("out/{name}/");
        output.iter().filter_map(|(path, _)| path.strip_prefix(prefix.as_bytes()).map(|rest| String::from_utf8(rest.to_vec()).unwrap())).collect()
    };
    assert_eq!(relation("parents"), ["bob/ann", "cat/ann", "dee/ann", "eve/gus", "hal/gus", "ivy/gus", "jon/bob", "jon/eve", "kim/bob", "kim/eve", "max/hal"]);
    assert_eq!(relation("mother"), ["bob/ann", "cat/ann", "dee/ann", "jon/eve", "kim/eve"]);
    assert_eq!(relation("sister"), ["bob/cat", "bob/dee", "cat/dee", "dee/cat", "eve/ivy", "hal/eve", "hal/ivy", "ivy/eve", "jon/kim"]);
    assert_eq!(relation("aunt"), ["jon/cat", "jon/dee", "jon/ivy", "kim/cat", "kim/dee", "kim/ivy", "max/eve", "max/ivy"]);
}
