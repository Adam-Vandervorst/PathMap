//! Traces some small programs, replays them, and checks the replay matches what really happened.  Each
//! test writes its animation to the test's temporary directory.  Run with `--nocapture` to see the paths

use std::io::{self, Write};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use pathmap::PathMap;
use pathmap::arena_compact::ArenaCompactTree;
use pathmap::utils::debug::TraceZipper;
use pathmap::utils::debug::zipper_tracing::{self, decode_trace};
use pathmap::zipper::*;
use tracer::{render_html, replay, Replay, ReplayConfig};

/// The trace is global, so tests that use it must not overlap
static TRACE_LOCK: Mutex<()> = Mutex::new(());

#[derive(Clone, Default)]
struct SharedBuf(Arc<Mutex<Vec<u8>>>);

impl Write for SharedBuf {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> { self.0.lock().unwrap().extend_from_slice(buf); Ok(buf.len()) }
    fn flush(&mut self) -> io::Result<()> { Ok(()) }
}

/// Runs `f` with a trace open, and returns the trace
fn traced(f: impl FnOnce()) -> Vec<u8> {
    let _lock = TRACE_LOCK.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    let buf = SharedBuf::default();
    zipper_tracing::open::<u64>(buf.clone()).unwrap();
    f();
    zipper_tracing::close().unwrap();
    let bytes = buf.0.lock().unwrap().clone();
    bytes
}

fn out_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("tracer")
}

/// Replays the trace, and writes it as `name.trace` and its animation as `name.html`
fn replay_and_render(name: &str, trace: &[u8], seeds: Vec<(String, PathMap<u64>)>) -> Replay<u64> {
    let events = decode_trace::<u64>(trace).unwrap();
    let replay = replay(&events, seeds, &ReplayConfig::default());
    assert!(replay.warnings.is_empty(), "{:?}", replay.warnings);
    std::fs::create_dir_all(out_dir()).unwrap();
    std::fs::write(out_dir().join(format!("{name}.trace")), trace).unwrap();
    let path = out_dir().join(format!("{name}.html"));
    std::fs::write(&path, render_html(&replay, name)).unwrap();
    println!("{name}: {}", path.display());
    replay
}

fn entries(map: &PathMap<u64>) -> Vec<(Vec<u8>, u64)> {
    map.iter().map(|(path, val)| (path, *val)).collect()
}

#[test]
fn one_zipper_assembles_paths() {
    let mut map = PathMap::<u64>::new();
    let trace = traced(|| {
        let mut wz = TraceZipper::new(1, map.write_zipper());
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
    let trace = traced(|| {
        let zh = map.zipper_head();
        let mut a = TraceZipper::new(1, zh.write_zipper_at_exclusive_path(b"ab/x/").unwrap());
        let mut b = TraceZipper::new(2, zh.write_zipper_at_exclusive_path(b"ab/y/").unwrap());
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
        let mut r = TraceZipper::new(3, zh.read_zipper_at_path(b"ab/y/").unwrap());
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
    let trace = traced(|| {
        let mut rz = TraceZipper::new(1, map.read_zipper());
        while rz.to_next_val() {}
        drop(rz);
        let mut wz = TraceZipper::new(2, map.write_zipper());
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
    let trace = traced(|| {
        //More children per node than are shown
        let mut wz = TraceZipper::new(1, map.write_zipper());
        for (idx, first) in (b'a'..=b'z').enumerate() {
            for second in b"xyz" {
                wz.set_val_at([first, *second], idx as u64);
            }
        }
        drop(wz);
        //Zippers at the root are on separate maps unless they reuse an id, so the reader reuses the writer's id
        let mut rz = TraceZipper::new(1, map.read_zipper());
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
