pub mod symbol_dump;
use pathmap::{
    // morphisms::Catamorphism,
    // utils::{ByteMask},
    trie_map::BytesTrieMap,
    arena_compact::ArenaCompactTree,
    // zipper::{Zipper, ZipperMoving, ZipperReadOnly}
};
use std::time::Instant;

fn arena_create() -> Result<(), std::io::Error> {
    // println!("in-memory dump");
    let sym_path = "../../../data/edges67458171.sym";
    let symtab = symbol_dump::SymbolMmap::new(sym_path).expect("can't open paths");
    let items = || symtab.iter();
    // let items = ["ace", "acf", "adg", "adh", "bjk"];
    // let items = || items.iter().copied();

    let start = Instant::now();
    let btm = BytesTrieMap::from_iter(items().map(|i| (i, ())));
    println!("built btm in {:.2?}", start.elapsed());
    // pathmap::alloc_tracking::read().print();
    // pathmap::alloc_tracking::reset();

    let start = Instant::now();
    let tree = ArenaCompactTree::from_zipper(btm.read_zipper(), |_v| 0);
    println!("built act in {:.2?}", start.elapsed());
    println!("counters {:?}", tree.counters());
    println!("len {:.2?}", tree.get_data().len());
    // pathmap::alloc_tracking::read().print();
    // pathmap::alloc_tracking::reset();
    pathmap::timed_span::print_counters();
    pathmap::timed_span::reset_counters();

    let start = Instant::now();
    let mut zipper = tree.read_zipper();
    for path in items() {
        use pathmap::zipper::ZipperMoving;
        zipper.reset();
        assert!(zipper.descend_to_existing(path) == path.len());
        // assert_eq!(zipper.path(), path);
    }
    pathmap::timed_span::print_counters();

    println!("checked act in {:.2?}", start.elapsed());
    let start = Instant::now();
    let tree2 = ArenaCompactTree::from_zipper(tree.read_zipper(), |_v| 0);
    assert_eq!(tree.get_data(), tree2.get_data());
    println!("cloned act in {:.2?}", start.elapsed());
    Ok(())
}

fn arena_dump() -> Result<(), std::io::Error> {
    // println!("fs dump");
    let sym_path = "../../../data/big.sym";
    let tree_path = "../../../data/big.tree";
    let symtab = symbol_dump::SymbolMmap::new(sym_path).expect("can't open paths");
    let items = || symtab.iter();
    // let items = ["ace", "acf", "adg", "adh", "bjk"];
    // let items = || items.iter().copied();

    let start = Instant::now();
    let btm = BytesTrieMap::from_iter(items().map(|i| (i, ())));
    println!("built btm in {:.2?}", start.elapsed());
    // pathmap::alloc_tracking::read().print();
    // pathmap::alloc_tracking::reset();

    let start = Instant::now();
    let tree = ArenaCompactTree::dump_from_zipper(
        btm.read_zipper(), |_v| 0, tree_path)?;
    println!("built act in {:.2?}", start.elapsed());
    println!("counters {:?}", tree.counters());
    println!("len {:.2?}", tree.get_data().len());
    // pathmap::alloc_tracking::read().print();
    // pathmap::alloc_tracking::reset();

    let start = Instant::now();
    let mut zipper = tree.read_zipper();
    for path in items() {
        use pathmap::zipper::ZipperMoving;
        zipper.reset();
        assert!(zipper.descend_to_existing(path) == path.len());
        // assert_eq!(zipper.path(), path);
    }
    pathmap::timed_span::print_counters();
    println!("checked act in {:.2?}", start.elapsed());
    let start = Instant::now();
    let tree2 = ArenaCompactTree::from_zipper(tree.read_zipper(), |_v| 0);
    assert_eq!(tree.get_data(), tree2.get_data());
    println!("cloned act in {:.2?}", start.elapsed());
    Ok(())
}

fn main() {
    // pathmap::alloc_tracking::init_tracking();
    arena_create().unwrap();
    arena_dump().unwrap();
    // println!("{:?}", pathmap::alloc_tracking::read());
}